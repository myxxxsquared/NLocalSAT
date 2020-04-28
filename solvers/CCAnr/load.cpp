
#include "satbasic.hpp"
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unistd.h>
#include <stdlib.h>

/*
 * Read in the problem.
 */
static int temp_lit[MAX_VARS]; //the max length of a clause can be MAX_VARS
static int build_instance(const char *filename)
{
    char line[1000000];
    char tempstr1[10];
    char tempstr2[10];
    int cur_lit;
    int i;
    int v, c;

    std::ifstream infile(filename);
    if (!infile)
        return 0;

    /*** build problem data structures of the instance ***/
    infile.getline(line, 1000000);
    while (line[0] != 'p')
        infile.getline(line, 1000000);

    sscanf(line, "%s %s %d %d", tempstr1, tempstr2, &num_vars, &num_clauses);
    ratio = double(num_clauses) / num_vars;

    if (num_vars >= MAX_VARS || num_clauses >= MAX_CLAUSES)
    {
        std::cout << "the size of instance exceeds out limitation, please enlarge MAX_VARS and (or) MAX_CLAUSES." << std::endl;
        exit(-1);
    }

    for (c = 0; c < num_clauses; c++)
    {
        clause_lit_count[c] = 0;
        clause_delete[c] = 0;
    }
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit_count[v] = 0;
        fix[v] = 0;
    }

    max_clause_len = 0;
    min_clause_len = num_vars;

    formula_len = 0;
    unitclause_queue_end_pointer = 0;

    //Now, read the clauses, one at a time.
    for (c = 0; c < num_clauses; c++)
    {
        infile >> cur_lit;

        while (cur_lit != 0)
        {
            temp_lit[clause_lit_count[c]] = cur_lit;
            clause_lit_count[c]++;

            infile >> cur_lit;
        }

        clause_lit[c] = new lit[clause_lit_count[c] + 1];

        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            clause_lit[c][i].clause_num = c;
            clause_lit[c][i].var_num = abs(temp_lit[i]);
            if (temp_lit[i] > 0)
                clause_lit[c][i].sense = 1;
            else
                clause_lit[c][i].sense = 0;

            var_lit_count[clause_lit[c][i].var_num]++;
        }
        clause_lit[c][i].var_num = 0;
        clause_lit[c][i].clause_num = -1;

        //unit clause
        if (clause_lit_count[c] == 1)
        {
            unitclause_queue[unitclause_queue_end_pointer++] = clause_lit[c][0];
            clause_delete[c] = 1;
        }

        if (clause_lit_count[c] > max_clause_len)
            max_clause_len = clause_lit_count[c];
        else if (clause_lit_count[c] < min_clause_len)
            min_clause_len = clause_lit_count[c];

        formula_len += clause_lit_count[c];
    }
    infile.close();

    avg_clause_len = (double)formula_len / num_clauses;

    if (unitclause_queue_end_pointer > 0)
    {
        simplify = 1;
        for (c = 0; c < num_clauses; c++)
        {
            org_clause_lit_count[c] = clause_lit_count[c];
            org_clause_lit[c] = new lit[clause_lit_count[c] + 1];
            for (i = 0; i < org_clause_lit_count[c]; ++i)
            {
                org_clause_lit[c][i] = clause_lit[c][i];
            }
        }
    }

    //creat var literal arrays
    for (v = 1; v <= num_vars; ++v)
    {
        var_lit[v] = new lit[var_lit_count[v] + 1];
        var_lit_count[v] = 0; //reset to 0, for build up the array
    }
    //scan all clauses to build up var literal arrays
    for (c = 0; c < num_clauses; ++c)
    {
        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            v = clause_lit[c][i].var_num;
            var_lit[v][var_lit_count[v]] = clause_lit[c][i];
            ++var_lit_count[v];
        }
    }
    for (v = 1; v <= num_vars; ++v) //set boundary
        var_lit[v][var_lit_count[v]].clause_num = -1;

    return 1;
}

static void build_neighbor_relation()
{
    int *neighbor_flag = new int[num_vars + 1];
    int i, j, count;
    int v, c;

    for (v = 1; v <= num_vars; ++v)
    {
        var_neighbor_count[v] = 0;

        if (fix[v] == 1)
            continue;

        for (i = 1; i <= num_vars; ++i)
            neighbor_flag[i] = 0;
        neighbor_flag[v] = 1;

        for (i = 0; i < var_lit_count[v]; ++i)
        {
            c = var_lit[v][i].clause_num;
            if (clause_delete[c] == 1)
                continue;

            for (j = 0; j < clause_lit_count[c]; ++j)
            {
                if (neighbor_flag[clause_lit[c][j].var_num] == 0)
                {
                    var_neighbor_count[v]++;
                    neighbor_flag[clause_lit[c][j].var_num] = 1;
                }
            }
        }

        neighbor_flag[v] = 0;

        var_neighbor[v] = new int[var_neighbor_count[v] + 1];

        count = 0;
        for (i = 1; i <= num_vars; ++i)
        {
            if (fix[i] == 1)
                continue;

            if (neighbor_flag[i] == 1)
            {
                var_neighbor[v][count] = i;
                count++;
            }
        }
        var_neighbor[v][count] = 0;
    }

    delete[] neighbor_flag;
    neighbor_flag = NULL;
}

static void unit_propagation()
{
    lit uc_lit;
    /*int uc_clause;*/
    int uc_var;
    bool uc_sense;

    int c /*,v*/;
    int i, j;
    lit cur /*, cur_c*/;

    //while (unitclause_queue_beg_pointer < unitclause_queue_end_pointer)
    for (unitclause_queue_beg_pointer = 0; unitclause_queue_beg_pointer < unitclause_queue_end_pointer; unitclause_queue_beg_pointer++)
    {
        uc_lit = unitclause_queue[unitclause_queue_beg_pointer];

        uc_var = uc_lit.var_num;
        uc_sense = uc_lit.sense;

        if (fix[uc_var] == 1)
        {
            if (uc_sense != cur_soln[uc_var])
                std::cout << "c wants to fix a variable twice, forbid." << std::endl;
            continue;
        }

        cur_soln[uc_var] = uc_sense; //fix the variable in unit clause
        fix[uc_var] = 1;

        for (i = 0; i < var_lit_count[uc_var]; ++i)
        {
            cur = var_lit[uc_var][i];
            c = cur.clause_num;

            if (clause_delete[c] == 1)
                continue;

            if (cur.sense == uc_sense) //then remove the clause from var's var_lit[] array
            {
                clause_delete[c] = 1;
            }
            else
            {
                if (clause_lit_count[c] == 2)
                {
                    if (clause_lit[c][0].var_num == uc_var)
                    {
                        unitclause_queue[unitclause_queue_end_pointer++] = clause_lit[c][1];
                    }
                    else
                    {
                        unitclause_queue[unitclause_queue_end_pointer++] = clause_lit[c][0];
                    }

                    clause_delete[c] = 1;
                }
                else
                {
                    for (j = 0; j < clause_lit_count[c]; ++j)
                    {
                        if (clause_lit[c][j].var_num == uc_var)
                        {
                            clause_lit[c][j] = clause_lit[c][clause_lit_count[c] - 1];

                            clause_lit_count[c]--;

                            break;
                        }
                    } //for
                }
            }

        } //for

    } //begpointer to endpointer for
}

static void preprocess()
{
    int c, v, i;
    int delete_clause_count = 0;
    int fix_var_count = 0;

    unit_propagation();

    //rescan all clauses to build up var literal arrays
    for (v = 1; v <= num_vars; ++v)
        var_lit_count[v] = 0;

    max_clause_len = 0;
    min_clause_len = num_vars;
    int formula_len = 0;

    for (c = 0; c < num_clauses; ++c)
    {
        if (clause_delete[c] == 1)
        {
            delete_clause_count++;
            continue;
        }

        for (i = 0; i < clause_lit_count[c]; ++i)
        {
            v = clause_lit[c][i].var_num;
            var_lit[v][var_lit_count[v]] = clause_lit[c][i];
            ++var_lit_count[v];
        }
        clause_lit[c][i].var_num = 0; //new clause boundary
        clause_lit[c][i].clause_num = -1;

        //about clause length
        formula_len += clause_lit_count[c];

        if (clause_lit_count[c] > max_clause_len)
            max_clause_len = clause_lit_count[c];
        else if (clause_lit_count[c] < min_clause_len)
            min_clause_len = clause_lit_count[c];
    }

    avg_clause_len = (double)formula_len / num_clauses;

    for (v = 1; v <= num_vars; ++v)
    {
        if (fix[v] == 1)
        {
            fix_var_count++;
        }
        var_lit[v][var_lit_count[v]].clause_num = -1; //new var_lit boundary
    }

    std::cout << "c unit propagation fixes " << fix_var_count << " variables, and delets " << delete_clause_count << " clauses" << std::endl;
}

#ifdef USE_RESULT

int build_result(char *filename)
{
    std::ifstream infile(filename);
    if (!infile)
        return 0;

    std::string line;

    while (std::getline(infile, line))
    {
        if (line[0] != 'v' || line[1] != ' ')
            continue;
        std::stringstream ss(line.substr(2));
        int curlit;
        while (ss >> curlit)
            if (curlit > 0)
                result_vars[curlit] = 1;
            else if (curlit < 0)
                result_vars[-curlit] = 0;
    }
    return 1;
}

#endif // USE_RESULT

bool load()
{
    if (build_instance(inst.c_str()) == 0)
    {
        std::cout << "Invalid filename: " << inst << std::endl;
        return false;
    }

    if (unitclause_queue_end_pointer > 0)
        preprocess();

    build_neighbor_relation();

    scale_ave = (threshold + 1) * q_scale;

#ifdef USE_RESULT
    build_result();
#endif // USE_RESULT

    return true;
}

void free_memory()
{
    int i;
    for (i = 0; i < num_clauses; i++)
    {
        delete[] clause_lit[i];
    }

    for (i = 1; i <= num_vars; ++i)
    {
        delete[] var_lit[i];
        delete[] var_neighbor[i];
    }
}

