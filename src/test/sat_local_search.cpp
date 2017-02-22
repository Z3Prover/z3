#include "sat_local_search.h"
#include "sat_solver.h"

static int build_instance(char *filename, sat::solver& s, sat::local_search& ls)
{
    char	line[16383];
    int	cur_term;
    // for temperally storage
    int	temp[16383];
    int	temp_count;

    std::ifstream infile(filename);
    //if (infile == NULL) //linux
    if (!infile)
        return 0;
    infile.getline(line, 16383);
    int num_vars, num_constraints;
    sscanf_s(line, "%d %d", &num_vars, &num_constraints);
    //cout << "number of variables: " << num_vars << endl;
    //cout << "number of constraints: " << num_constraints << endl;


    // write in the objective function
    temp_count = 0;
    infile >> cur_term;
    while (cur_term != 0) {
        temp[temp_count++] = cur_term;
        infile >> cur_term;
    }
    int ob_num_terms = temp_count;

#if 0
    TBD make this compile:
    ob_constraint = new ob_term[ob_num_terms + 1];
    // coefficient
    ob_constraint[0].coefficient = 0;	// virtual var: all variables not in ob are pointed to this var
    for (i = 1; i <= ob_num_terms; ++i) {
        ob_constraint[i].coefficient = temp[i - 1];
    }

    sat::literal_vector lits;
    // ob variable
    temp_count = 0;
    infile >> cur_term;
    while (cur_term != 0) {
        temp[temp_count++] = cur_term;
        infile >> cur_term;
    }
    if (temp_count != ob_num_terms) {
        cout << "Objective function format error." << endl;
        exit(-1);
    }
    for (i = 1; i <= ob_num_terms; ++i) {
        ob_constraint[i].var_id = temp[i - 1];
        coefficient_in_ob_constraint[ob_constraint[i].var_id] = ob_constraint[i].coefficient;
    }
    // read the constraints, one at a time
    card_extension* ext = 0;
    int k;
    for (c = 1; c <= num_constraints; ++c) {        
        lits.reset();
        infile >> cur_term;
        while (cur_term != 0) {
            lits.push_back(sat::literal(abs(cur_term), cur_term > 0));
            infile >> cur_term;
        }
        infile >> k;
        ext->add_at_least(null_bool_var, lits, lits.size() - k);
    }
#endif

    infile.close();


#if 0
    Move all of this to initialization code for local search solver:

    // create var_term array
    for (v = 1; v <= num_vars; ++v) {
        var_term[v] = new term[var_term_count[v]];
        var_term_count[v] = 0; // reset to 0, for building up the array
    }
    // scan all constraints to build up var term arrays
    for (c = 1; c <= num_constraints; ++c) {
        for (i = 0; i < constraint_term_count[c]; ++i) {
            v = constraint_term[c][i].var_id;
            var_term[v][var_term_count[v]++] = constraint_term[c][i];
        }
    }


    // build neighborhood relationship
    bool *is_neighbor;
    is_neighbor = new bool[num_vars + 1];
    for (v = 1; v <= num_vars; ++v) {
        // init as not neighbor
        for (i = 1; i <= num_vars; ++i) {
            is_neighbor[i] = false;
        }
        temp_count = 0;
        // for each constraint v appears
        for (i = 0; i < var_term_count[v]; ++i) {
            c = var_term[v][i].constraint_id;
            for (j = 0; j < constraint_term_count[c]; ++j) {
                if (constraint_term[c][j].var_id == v)
                    continue;
                // not neighbor yet
                if (!is_neighbor[constraint_term[c][j].var_id]) {
                    is_neighbor[constraint_term[c][j].var_id] = true;
                    temp[temp_count++] = constraint_term[c][j].var_id;
                }
            }
        }
        // create and build neighbor
        var_neighbor_count[v] = temp_count;
        var_neighbor[v] = new int[var_neighbor_count[v]];
        for (i = 0; i < var_neighbor_count[v]; ++i) {
            var_neighbor[v][i] = temp[i];
        }
    }
    delete[] is_neighbor;

#endif
    return 1;
}

void tst_sat_local_search(char ** argv, int argc, int& i) {
    if (argc != i + 2) {
        std::cout << "require dimacs file name\n";
        return;
    }
    // sat::solver s;
    // populate the sat solver with clauses and cardinality consrtaints from the input
    // call the lookahead solver.
    // TBD
}
