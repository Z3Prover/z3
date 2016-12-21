/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    arith_eq_solver.cpp

Abstract:

    Solver for linear arithmetic equalities.

Author:

    Nikolaj Bjorner (nbjorner) 2012-02-25
    
--*/
#include"arith_eq_solver.h"


arith_eq_solver::~arith_eq_solver() {
}

arith_eq_solver::arith_eq_solver(ast_manager & m, params_ref const& p):
    m(m),
    m_params(p),
    m_util(m),
    m_arith_rewriter(m)
{
    m_params.set_bool("gcd_rounding", true);
    // m_params.set_bool("sum", true);
    m_arith_rewriter.updt_params(m_params);
}


/**
   \brief Return true if the first monomial of t is negative.
*/
bool arith_eq_solver::is_neg_poly(expr * t) const {
    if (m_util.is_add(t)) {
        t = to_app(t)->get_arg(0);
    }
    if (m_util.is_mul(t)) {
        t = to_app(t)->get_arg(0);
        rational r;
        bool is_int;
        if (m_util.is_numeral(t, r, is_int))
            return r.is_neg();
    }
    return false;
}


void arith_eq_solver::prop_mod_const(expr * e, unsigned depth, numeral const& k, expr_ref& result) {
    SASSERT(m_util.is_int(e));
    SASSERT(k.is_int() && k.is_pos());
    numeral n;
    bool is_int;

    if (depth == 0) {
        result = e;
    }
    else if (m_util.is_add(e) || m_util.is_mul(e)) {
        expr_ref_vector args(m);
        expr_ref tmp(m);
        app* a = to_app(e);
        for (unsigned i = 0; i < a->get_num_args(); ++i) {
            prop_mod_const(a->get_arg(i), depth - 1, k, tmp);
            args.push_back(tmp);
        }
        m_arith_rewriter.mk_app(a->get_decl(), args.size(), args.c_ptr(), result);
    }
    else if (m_util.is_numeral(e, n, is_int) && is_int) {
        result = m_util.mk_numeral(mod(n, k), true);
    }
    else {
        result = e;
    }
}

void arith_eq_solver::gcd_normalize(vector<numeral>& values) {
    numeral g(0);
    for (unsigned i = 0; !g.is_one() && i < values.size(); ++i) {
        SASSERT(values[i].is_int());
        if (!values[i].is_zero()) {
            if (g.is_zero()) {
                g = abs(values[i]);
            }
            else {
                g = gcd(abs(values[i]), g);
            }
        }
    }
    if (g.is_zero() || g.is_one()) {
        return;
    }
    for (unsigned i = 0; i < values.size(); ++i) {
        values[i] = values[i] / g;
        SASSERT(values[i].is_int());
    }
}

unsigned arith_eq_solver::find_abs_min(vector<numeral>& values) {
    SASSERT(values.size() >= 2);
    unsigned index = 0;
    numeral v(0);
    for (unsigned i = 1; i < values.size(); ++i) {
        numeral w = abs(values[i]);
        if (v.is_zero() || (!w.is_zero() && w < v)) {
            index = i;
            v = w;
        }
    }
    return index;
}

#ifdef _TRACE

static void print_row(std::ostream& out, vector<rational> const& row) {
    for(unsigned i = 0; i < row.size(); ++i) { 
        out << row[i] << " "; 
    } 
    out << "\n";
}

static void print_rows(std::ostream& out, vector<vector<rational> > const& rows) {
    for (unsigned i = 0; i < rows.size(); ++i) {
        print_row(out, rows[i]);
    }
}
#endif

//
// The gcd of the coefficients to variables have to divide the
// coefficient to the constant.
// The constant is the last value in the array.
//
bool arith_eq_solver::gcd_test(vector<numeral>& values) {
    SASSERT(values.size() > 0);
    numeral g(0);
    numeral first_value = values[0];
    for (unsigned i = 1; !g.is_one() && i < values.size(); ++i) {
        if (!values[i].is_zero()) {
            if (g.is_zero()) {
                g = abs(values[i]);
            }
            else {
                g = gcd(abs(values[i]), g);
            }
        }
    }
    if (g.is_one()) {
        return true;
    }
    if (g.is_zero()) {
        return first_value.is_zero();
    }
    numeral r = first_value/g;
    return r.is_int();
}


bool arith_eq_solver::solve_integer_equation(
    vector<numeral>& values,
    unsigned&        index,
    bool&            is_fresh
    )
{
    TRACE("arith_eq_solver", 
          tout << "solving: ";
          print_row(tout, values);
          );
    //
    // perform one step of the omega test equality elimination.
    //
    // Given:
    //    a1*x1 + a2*x2 + .. + a_n*x_n + a_{n+1} = 0
    // 
    // Assume gcd(a1,..,a_n,a_{n+1}) = 1
    // Assume gcd(a1,...,a_n) divides a_{n+1} (eg. gcd(a1,..,an) = 1)
    // 
    // post-condition: values[index] = -1.
    // 
    // Let a_index be index of least absolute value.
    //
    // If |a_index| = 1, then return row and index.
    // Otherwise:
    //  Let m = |a_index| + 1
    //  Set
    // 
    //    m*x_index' 
    // =  
    //    ((a1 mod_hat m)*x1 + (a2 mod_hat m)*x2 + .. + (a_n mod_hat m)*x_n + (k mod_hat m))
    // = 
    //    (a1'*x1 + a2'*x2 + .. (-)1*x_index + ...)
    // 
    // <=> Normalize signs so that sign to x_index is -1.
    //    (-)a1'*x1 + (-)a2'*x2 + .. -1*x_index + ... + m*x_index'  = 0
    // 
    // Return row, where the coefficient to x_index is implicit.
    // Instead used the coefficient 'm' at position 'index'.
    // 

    gcd_normalize(values);
    if (!gcd_test(values)) {
        TRACE("arith_eq_solver", tout << "not sat\n";
              print_row(tout, values););
        return false;
    }
    index = find_abs_min(values);
    SASSERT(1 <= index && index < values.size());
    numeral a = values[index];
    numeral abs_a = abs(a);

    if (abs_a.is_zero()) {
        // The equation is trivial.
        return true;
    }
    if (a.is_one()) {
        for (unsigned i = 0; i < values.size(); ++i) {
            values[i].neg();
        }
    }
    is_fresh = !abs_a.is_one();

    if (is_fresh) {

        numeral m = abs_a + numeral(1);
        for (unsigned i = 0; i < values.size(); ++i) {
            values[i] = mod_hat(values[i], m);
        }
        if (values[index].is_one()) {
            for (unsigned i = 0; i < values.size(); ++i) {
                values[i].neg();
            }
        }
        SASSERT(values[index].is_minus_one());
        values[index] = m;
    }

    TRACE("arith_eq_solver", 
          tout << "solved at index " << index << ": ";
          print_row(tout, values);
          );

    return true;
}


void arith_eq_solver::substitute(
    row&       r,
    row const& s,
    unsigned   index
    )
{
    SASSERT(1 <= index && index < s.size());
    TRACE("arith_eq_solver", 
          tout << "substitute " << index << ":\n";
          print_row(tout, r);
          print_row(tout, s);
          );

    if (index >= r.size()) {
        return;
    }

    numeral c = r[index];
    if (c.is_zero()) {
        // no-op
    }
    else if (abs(s[index]).is_one()) {
        //
        // s encodes an equation that contains a variable
        // with a unit coefficient.
        //
        // Let 
        //  c = r[index]
        //  s = s[index]*x + s'*y = 0
        //  r = c*x + r'*y = 0
        // 
        // => 
        //
        //   0
        // = 
        //   -sign(s[index])*c*s + r 
        // =  
        //   -s[index]*sign(s[index])*c*x - sign(s[index])*c*s'*y + c*x + r'*y
        // = 
        //   -c*x - sign(s[index])*c*s'*y + c*x + r'*y
        // = 
        //   -sign(s[index])*c*s'*y + r'*y
        //
        numeral sign_s = s[index].is_pos()?numeral(1):numeral(-1);
        for (unsigned i = 0; i < r.size(); ++i) {
            r[i] -= c*sign_s*s[i];
        }
        for (unsigned i = r.size(); i < s.size(); ++i) {
            r.push_back(-c*sign_s*s[i]);
        }
    }
    else {
        //
        // s encodes a substitution using an auxiliary variable.
        // the auxiliary variable is at position 'index'.
        // 
        // Let 
        //  c = r[index]
        //  s = s[index]*x + s'*y = 0
        //  r = c*x + r'*y = 0
        //
        //  s encodes : x |-> s[index]*x' + s'*y
        //
        //  Set: 
        //
        //    r := c*s + r'*y
        // 
        r[index] = numeral(0);
        for (unsigned i = 0; i < r.size(); ++i) {
            r[i] += c*s[i];
        }        
        for (unsigned i = r.size(); i < s.size(); ++i) {
            r.push_back(c*s[i]);
        }

    }    

    TRACE("arith_eq_solver", 
          tout << "result: ";
          print_row(tout, r);
          );
}

bool arith_eq_solver::solve_integer_equations(
    vector<row>& rows, 
    row&         unsat_row
    )
{
    // return solve_integer_equations_units(rows, unsat_row);
    return solve_integer_equations_gcd(rows, unsat_row);
}

//
// Naive integer equation solver where only units are eliminated.
// 

bool arith_eq_solver::solve_integer_equations_units(
    vector<row>&   rows, 
    row&           unsat_row
    )
{

    TRACE("arith_eq_solver", print_rows(tout << "solving:\n", rows););

    unsigned_vector todo, done;
    
    for (unsigned i = 0; i < rows.size(); ++i) {
        todo.push_back(i);
        row& r = rows[i];
        gcd_normalize(r);
        if (!gcd_test(r)) {
            unsat_row = r;
            TRACE("arith_eq_solver", print_row(tout << "input is unsat: ", unsat_row); );
            return false;
        }        
    }
    for (unsigned i = 0; i < todo.size(); ++i) {        
        row& r = rows[todo[i]];
        gcd_normalize(r);
        if (!gcd_test(r)) {
            unsat_row = r;
            TRACE("arith_eq_solver", print_row(tout << "unsat: ", unsat_row); );
            return false;
        }
        unsigned index = find_abs_min(r);
        SASSERT(1 <= index && index < r.size());
        numeral a = r[index];
        numeral abs_a = abs(a);
        if (abs_a.is_zero()) {
            continue;
        }
        else if (abs_a.is_one()) {
            for (unsigned j = i+1; j < todo.size(); ++j) {
                substitute(rows[todo[j]], r, index);
            }
            for (unsigned j = 0; j < done.size(); ++j) {
                row& r2 = rows[done[j]];
                if (!r2[index].is_zero()) {
                    substitute(r2, r, index);
                    todo.push_back(done[j]);
                    done.erase(done.begin()+j);
                    --j;
                }                
            }
        }
        else {
            done.push_back(todo[i]);
        }
    }

    TRACE("arith_eq_solver", 
          tout << ((done.size()<=1)?"solved ":"incomplete check ") << done.size() << "\n";
          for (unsigned i = 0; i < done.size(); ++i) {
              print_row(tout, rows[done[i]]);
          }
          );

    return true;
}




//
// Partial solver based on the omega test equalities.
// unsatisfiability is not preserved when eliminating 
// auxiliary variables.
//

bool arith_eq_solver::solve_integer_equations_omega(
    vector<row> & rows, 
    row&        unsat_row
    )
{
    unsigned index;
    bool is_fresh;
    vector<row>     rows_solved;
    unsigned_vector indices;
    unsigned_vector aux_indices;


    for (unsigned i = 0; i < rows.size(); ++i) {
        rows_solved.push_back(rows[i]);
        row& r = rows_solved.back();
        for (unsigned j = 0; j + 1 < rows_solved.size(); ++j) {
            substitute(r, rows_solved[j], indices[j]);
        }
        if (!solve_integer_equation(r, index, is_fresh)) {
            unsat_row = r;
            gcd_normalize(unsat_row);
            // invert the substitution for every index that is fresh.

            TRACE("arith_eq_solver",
                  tout << "unsat:\n";
                  print_row(tout, unsat_row);
                  for (unsigned l = 0; l + 1< rows_solved.size(); ++l) {
                      print_row(tout, rows_solved[l]);
                  });

            for (unsigned j = rows_solved.size()-1; j > 0; ) {
                --j;
                row& solved_row = rows_solved[j];
                unsigned index_j = indices[j];
                unsigned aux_index_j = aux_indices[j];
                SASSERT(index_j <= aux_index_j);
                if (unsat_row.size() <= aux_index_j) {
                    unsat_row.resize(aux_index_j+1);
                }
                numeral m = solved_row[aux_index_j];
                numeral k = unsat_row[aux_index_j];
                if (aux_index_j != index_j && !k.is_zero()) {
                    //
                    // solved_row: -x_index +  m*sigma + r1 = 0
                    // unsat_row:      k*sigma + r2 = 0
                    // 
                    // <=> 
                    // 
                    // solved_row: -k*x_index +  k*m*sigma + k*r1 = 0
                    // unsat_row:      m*k*sigma + m*r2 = 0
                    //
                    // =>
                    //
                    // m*k*sigma + m*r2 + k*x_index - k*m*sigma - k*r1 = 0
                    // 
                    for (unsigned l = 0; l < unsat_row.size(); ++l) {
                        unsat_row[l] *= m;
                        unsat_row[l] -= k*solved_row[l];
                    }
                    for (unsigned l = unsat_row.size(); l < solved_row.size(); ++l) {
                        unsat_row.push_back(solved_row[l]);
                    }

                    gcd_normalize(unsat_row);
                    TRACE("arith_eq_solver", 
                          tout << "gcd: ";
                          print_row(tout, solved_row);
                          print_row(tout, unsat_row);
                          );

                }
                if (gcd_test(unsat_row)) {
                    TRACE("arith_eq_solver", tout << "missed pure explanation\n";);
                    return true;
                }
                SASSERT(!gcd_test(unsat_row));
            }
            return false;
        }
        else if (r[index].is_zero()) {
            // Row is trival
            rows_solved.pop_back();
            continue;
        }
        else if (!abs(r[index]).is_one()) {
            //
            // The solution introduces a fresh auxiliary variable.
            // Make space for this variable as a fresh numeral.
            //
            indices.push_back(index);
            aux_indices.push_back(r.size());

            r.push_back(r[index]);
            r[index] = numeral(-1);

            // re-solve the same row.
            --i;
        }
        else {
            indices.push_back(index);
            aux_indices.push_back(index);
        }
    }
    return true;
}



//
// Eliminate variables by searching for combination of rows where
// the coefficients have gcd = 1. 
// 

bool arith_eq_solver::solve_integer_equations_gcd(
    vector<row> & rows, 
    row&        unsat_row
    )
{    
    unsigned_vector live, useful, gcd_pos;
    vector<rational> gcds;
    rational u, v;
    
    if (rows.empty()) {
        return true;
    }
    for (unsigned i = 0; i < rows.size(); ++i) {
        live.push_back(i);
        row& r = rows[i];
        gcd_normalize(r);
        if (!gcd_test(r)) {
            unsat_row = r;
            TRACE("arith_eq_solver", print_row(tout << "input is unsat: ", unsat_row); );
            return false;
        }        
    }
    unsigned max_column = rows[0].size();
    bool change = true;
    while (change && !live.empty()) {
        change = false;
        for (unsigned i = 1; i < max_column; ++i) {
            rational g(0);
            gcds.reset();
            gcd_pos.reset();
            unsigned j = 0;
            for (; j < live.size(); ++j) {
                rational const& k = rows[live[j]][i];
                if (k.is_zero()) {
                    continue;
                }
                if (g.is_zero()) {
                    g = abs(k);
                }
                else {
                    g = gcd(g, abs(k));
                }
                if (abs(g).is_one()) {
                    break;
                }
                gcds.push_back(g);
                gcd_pos.push_back(live[j]);
            }
            if (j == live.size()) {
                continue;
            }
            
            change = true;
            // found gcd, now identify reduced set of rows with GCD = 1.
            g = abs(rows[live[j]][i]);
            useful.push_back(live[j]);
            unsigned live_pos = j;
            for (j = gcds.size(); !g.is_one() && j > 0; ) {
                SASSERT(g.is_pos());
                --j;
                if (j == 0 || !gcd(g, gcds[j-1]).is_one()) {
                    useful.push_back(gcd_pos[j]);
                    g = gcd(g, gcds[j]);
                    SASSERT(j == 0 || gcd(g,gcds[j-1]).is_one());
                }                
            }
            //
            // we now have a set "useful" of rows whose combined GCD = 1.
            // pivot the remaining with the first row.
            //
            row& r0 = rows[useful[0]];
            for (j = 1; j < useful.size(); ++j) {
                row& r1 = rows[useful[j]];          
                g = gcd(r0[i], r1[i], u, v);
                for (unsigned k = 0; k < max_column; ++k) {
                    r0[k] = u*r0[k] + v*r1[k];
                }
                SASSERT(g == r0[i]);
            }
            if (!abs(r0[i]).is_one()) {
                return false;
            }
            live.erase(live.begin()+live_pos);
            for (j = 0; j < live.size(); ++j) {
                row& r = rows[live[j]];
                if (!r[i].is_zero()) {
                    substitute(r, r0, i);
                    gcd_normalize(r);
                    if (!gcd_test(r)) {
                        unsat_row = r;
                        TRACE("arith_eq_solver", print_row(tout << "unsat: ", unsat_row); );
                        return false;
                    }
                }
            }
        }
    }

    TRACE("arith_eq_solver", 
          tout << ((live.size()<=1)?"solved ":"incomplete check ") << live.size() << "\n";
          for (unsigned i = 0; i < live.size(); ++i) {
              print_row(tout, rows[live[i]]);
          }
          );

    return true;
}
