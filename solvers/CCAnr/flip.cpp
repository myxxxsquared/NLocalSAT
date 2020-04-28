
#include "satbasic.hpp"

void unsat(int clause)
{
    index_in_unsat_stack[clause] = unsat_stack_fill_pointer;
    push(clause, unsat_stack);

    //update appreance count of each var in unsat clause and update stack of vars in unsat clauses
    int v;
    for (lit *p = clause_lit[clause]; (v = p->var_num) != 0; p++)
    {
        unsat_app_count[v]++;
        if (unsat_app_count[v] == 1)
        {
            index_in_unsatvar_stack[v] = unsatvar_stack_fill_pointer;
            push(v, unsatvar_stack);
        }
    }
}

void sat(int clause)
{
    int index, last_unsat_clause;

    //since the clause is satisfied, its position can be reused to store the last_unsat_clause
    last_unsat_clause = pop(unsat_stack);
    index = index_in_unsat_stack[clause];
    unsat_stack[index] = last_unsat_clause;
    index_in_unsat_stack[last_unsat_clause] = index;

    //update appreance count of each var in unsat clause and update stack of vars in unsat clauses
    int v, last_unsat_var;
    for (lit *p = clause_lit[clause]; (v = p->var_num) != 0; p++)
    {
        unsat_app_count[v]--;
        if (unsat_app_count[v] == 0)
        {
            last_unsat_var = pop(unsatvar_stack);
            index = index_in_unsatvar_stack[v];
            unsatvar_stack[index] = last_unsat_var;
            index_in_unsatvar_stack[last_unsat_var] = index;
        }
    }
}

void flip(int flipvar)
{
    cur_soln[flipvar] = 1 - cur_soln[flipvar];

    int v, c;
    lit *clause_c;

    int org_flipvar_score = score[flipvar];

    //update related clauses and neighbor vars
    for (lit *q = var_lit[flipvar]; (c = q->clause_num) >= 0; q++)
    {
        clause_c = clause_lit[c];
        if (cur_soln[flipvar] == q->sense)
        {
            ++sat_count[c];

            if (sat_count[c] == 2) //sat_count from 1 to 2
                score[sat_var[c]] += clause_weight[c];
            else if (sat_count[c] == 1) // sat_count from 0 to 1
            {
                sat_var[c] = flipvar; //record the only true lit's var
                for (lit *p = clause_c; (v = p->var_num) != 0; p++)
                    score[v] -= clause_weight[c];

                sat(c);
            }
        }
        else // cur_soln[flipvar] != cur_lit.sense
        {
            --sat_count[c];
            if (sat_count[c] == 1) //sat_count from 2 to 1
            {
                for (lit *p = clause_c; (v = p->var_num) != 0; p++)
                {
                    if (p->sense == cur_soln[v])
                    {
                        score[v] -= clause_weight[c];
                        sat_var[c] = v;
                        break;
                    }
                }
            }
            else if (sat_count[c] == 0) //sat_count from 1 to 0
            {
                for (lit *p = clause_c; (v = p->var_num) != 0; p++)
                    score[v] += clause_weight[c];
                unsat(c);
            } //end else if

        } //end else
    }

    score[flipvar] = -org_flipvar_score;

    /*update CCD */
    int index;

    conf_change[flipvar] = 0;
    //remove the vars no longer goodvar in goodvar stack
    for (index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
    {
        v = goodvar_stack[index];
        if (score[v] <= 0)
        {
            goodvar_stack[index] = pop(goodvar_stack);
            already_in_goodvar_stack[v] = 0;
        }
    }

    //update all flipvar's neighbor's conf_change to be 1, add goodvar
    int *p;
    for (p = var_neighbor[flipvar]; (v = *p) != 0; p++)
    {
        conf_change[v] = 1;

        if (score[v] > 0 && already_in_goodvar_stack[v] == 0)
        {
            push(v, goodvar_stack);
            already_in_goodvar_stack[v] = 1;
        }
    }
}
