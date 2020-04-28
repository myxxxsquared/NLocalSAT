
#include "satbasic.hpp"

#include <stdlib.h>

void smooth_clause_weights()
{
    int /*i,*/ j, c, v;
    int new_total_weight = 0;

    for (v = 1; v <= num_vars; ++v)
    {
#ifdef USE_CHANGED_WEIGHT
        switch (cnf_predict.output[v - 1])
        {
        case 0:
        case 1:
        case 4:
        case 5:
            score[v] = 30;
            break;
        case 2:
        case 3:
            score[v] = 10;
            break;
        }

        switch (cnf_predict.output[v - 1])
        {
        case 0:
        case 1:
        case 2:
            if (cur_soln[v] == 0)
                score[v] = -score[v];
            break;
        case 3:
        case 4:
        case 5:
            if (cur_soln[v] == 1)
                score[v] = -score[v];
            break;
        }
#else
        score[v] = 0;
#endif
    }

    //smooth clause score and update score of variables
    for (c = 0; c < num_clauses; ++c)
    {
        clause_weight[c] = clause_weight[c] * p_scale + scale_ave;
        if (clause_weight[c] < 1)
            clause_weight[c] = 1;

        new_total_weight += clause_weight[c];

        //update score of variables in this clause
        if (sat_count[c] == 0)
        {
            for (j = 0; j < clause_lit_count[c]; ++j)
            {
                score[clause_lit[c][j].var_num] += clause_weight[c];
            }
        }
        else if (sat_count[c] == 1)
            score[sat_var[c]] -= clause_weight[c];
    }

    ave_weight = new_total_weight / num_clauses;
}

void update_clause_weights()
{
    int i, v;

    for (i = 0; i < unsat_stack_fill_pointer; ++i)
        clause_weight[unsat_stack[i]]++;

    for (i = 0; i < unsatvar_stack_fill_pointer; ++i)
    {
        v = unsatvar_stack[i];
        score[v] += unsat_app_count[v];
        if (score[v] > 0 && conf_change[v] == 1 && already_in_goodvar_stack[v] == 0)
        {
            push(v, goodvar_stack);
            already_in_goodvar_stack[v] = 1;
        }
    }

    delta_total_weight += unsat_stack_fill_pointer;
    if (delta_total_weight >= num_clauses)
    {
        ave_weight += 1;
        delta_total_weight -= num_clauses;

        //smooth weights
        if (ave_weight > threshold)
            smooth_clause_weights();
    }
}

int pick_var(void)
{
    int i, k, c, v;
    int best_var;
    lit *clause_c;

    /**Greedy Mode**/
    /*CCD (configuration changed decreasing) mode, the level with configuation chekcing*/
    if (goodvar_stack_fill_pointer > 0)
    {
        best_var = goodvar_stack[0];
        for (i = 1; i < goodvar_stack_fill_pointer; ++i)
        {
            v = goodvar_stack[i];
            if (score[v] > score[best_var])
                best_var = v;
            else if (score[v] == score[best_var])
            {
                //if(unsat_app_count[v]>unsat_app_count[best_var]) best_var = v;
                //else if(unsat_app_count[v]==unsat_app_count[best_var]&&time_stamp[v]<time_stamp[best_var]) best_var = v;

                if (time_stamp[v] < time_stamp[best_var])
                    best_var = v;
            }
        }
        return best_var;
    }

    /*aspiration*/
    if (aspiration_active)
    {
        best_var = 0;
        for (i = 0; i < unsatvar_stack_fill_pointer; ++i)
        {
            if (score[unsatvar_stack[i]] > ave_weight)
            {
                best_var = unsatvar_stack[i];
                break;
            }
        }

        for (++i; i < unsatvar_stack_fill_pointer; ++i)
        {
            v = unsatvar_stack[i];
            if (score[v] > score[best_var])
                best_var = v;
            else if (score[v] == score[best_var] && time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }

        if (best_var != 0)
        {
            return best_var;
        }
        }
    /*****end aspiration*******************/

    update_clause_weights();

    /*focused random walk*/

    c = unsat_stack[rand() % unsat_stack_fill_pointer];
    clause_c = clause_lit[c];
    best_var = clause_c[0].var_num;
    for (k = 1; k < clause_lit_count[c]; ++k)
    {
#ifdef USE_NR
        v = clause_c[k].var_num;

        if (unsat_app_count[v] > unsat_app_count[best_var])
            best_var = v;
        else if (unsat_app_count[v] == unsat_app_count[best_var])
        {
            if (score[v] > score[best_var])
                best_var = v;
            else if (score[v] == score[best_var] && time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }
#else  //USE_NR
        if (time_stamp[v] < time_stamp[best_var])
            best_var = v;
#endif //USE_NR
    }

    return best_var;
}
