
#include "satbasic.hpp"

#include <stdlib.h>
#include <stdio.h>

//initiation of the algorithm
static void init()
{
    int v, c;
    int i, j;

    //Initialize edge weights
    for (c = 0; c < num_clauses; c++)
        clause_weight[c] = 1;

    //init unsat_stack
    unsat_stack_fill_pointer = 0;
    unsatvar_stack_fill_pointer = 0;

    //init solution
    for (v = 1; v <= num_vars; v++)
    {

        if (fix[v] == 0)
        {
#if defined USE_INIT_PREDICT
            cur_soln[v] = (int)(rand() % 100 >= 90) ^ cnf_predict.output[v - 1];
            // tryside = tryside ^ 1;
            // printf("HERE\n");
            // const int randmul = 10000;
            // int randval = int(tryrage * randmul);
            // tryrage = tryrage * 0.95;
            // cur_soln[v] = (rand() % randmul > randval) ? (rand() % 2) : (cnf_predict.output[v - 1]);
            // cur_soln[v] = cnf_predict.output[v - 1] = (rand() % 100 >= 90) ? (rand() % 2) : cnf_predict.output[v - 1];
            // switch (cnf_predict.output[v - 1])
            // {
            // case 0:
            //     cur_soln[v] = (rand() % 100 >= 90) ? 1 : 0;
            //     // cur_soln[v] = 0;
            //     break;
            // case 1:
            //     // cur_soln[v] = 1;
            //     cur_soln[v] = (rand() % 100 >= 90) ? 0 : 1;
            //     break;
            //     // case 2:
            //     //     cur_soln[v] = (rand() % 100 >= 50) ? 1 : 0;
            //     //     // cur_soln[v] = 0;
            //     //     break;
            //     // case 3:
            //     // case 4:
            //     //     cur_soln[v] = (rand() % 100 >= 50) ? 1 : 0;
            //     //     break;
            //     // case 5:
            //     //     // cur_soln[v] = (rand() % 100 >= 10) ? 1 : 0;
            //     //     cur_soln[v] = 1;
            //     //     // cur_soln[v] = 1;
            //     //     break;
            // }
#elif defined USE_RESULT
            if (rand() < samerate)
                cur_soln[v] = result_vars[v];
            else
                cur_soln[v] = int(!result_vars[v]);
#else
            cur_soln[v] = rand() % 2;
#endif

            time_stamp[v] = 0;
            conf_change[v] = 1;
            unsat_app_count[v] = 0;
        }
    }

    /* figure out sat_count, and init unsat_stack */
    for (c = 0; c < num_clauses; ++c)
    {
        if (clause_delete[c] == 1)
            continue;

        sat_count[c] = 0;

        for (j = 0; j < clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                sat_count[c]++;
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }

        if (sat_count[c] == 0)
            unsat(c);
    }

    /*figure out var score*/
    int lit_count;
    for (v = 1; v <= num_vars; v++)
    {
        if (fix[v] == 1)
        {
            score[v] = -100000;
            continue;
        }

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

        lit_count = var_lit_count[v];

        for (i = 0; i < lit_count; ++i)
        {
            c = var_lit[v][i].clause_num;
            if (sat_count[c] == 0)
                score[v]++;
            else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
                score[v]--;
        }
    }

    //init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for (v = 1; v <= num_vars; v++)
    {
        if (fix[v] == 1)
            continue;
        if (score[v] > 0) // && conf_change[v]==1)
        {
            already_in_goodvar_stack[v] = 1;
            push(v, goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = 0;
    }

    //setting for the virtual var 0
    time_stamp[0] = 0;

    this_try_best_unsat_stack_fill_pointer = unsat_stack_fill_pointer;
}

void local_search(long long no_improv_times)
{
    init();

    if (unsat_stack_fill_pointer == 0)
    {
        return;
    }

    int flipvar;
    long long notime = 1 + no_improv_times;

    while (--notime)
    {
        step++;
        if (step < 0)
        {
            step = 0; // steps should += 2**63
            printf("o\n");
        }

        flipvar = pick_var();
        flip(flipvar);
        time_stamp[flipvar] = step;

        if (unsat_stack_fill_pointer < this_try_best_unsat_stack_fill_pointer)
        {
            this_try_best_unsat_stack_fill_pointer = unsat_stack_fill_pointer;
            notime = 1 + no_improv_times;
        }

        if (unsat_stack_fill_pointer == 0)
        {
            return;
        }
    }

    return;
}
