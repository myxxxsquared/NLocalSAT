
#include <iostream>

#include "satbasic.hpp"

void print_information()
{
    std::cout << "c Instance: Number of variables = " << num_vars << std::endl;
    std::cout << "c Instance: Number of clauses = " << num_clauses << std::endl;
    std::cout << "c Instance: Ratio = " << ratio << std::endl;
    std::cout << "c Instance: Formula length = " << formula_len << std::endl;
    std::cout << "c Instance: Avg (Min,Max) clause length = " << avg_clause_len << " (" << min_clause_len << "," << max_clause_len << ")" << std::endl;
    std::cout << "c Algorithmic: Random seed = " << seed << std::endl;
    std::cout << "c Algorithmic: ls_no_improv_steps = " << ls_no_improv_times << std::endl;
    std::cout << "c Algorithmic: swt_p = " << p_scale << std::endl;
    std::cout << "c Algorithmic: swt_q = " << q_scale << std::endl;
    std::cout << "c Algorithmic: swt_threshold = " << threshold << std::endl;
    std::cout << "c Algorithmic: scale_ave = " << scale_ave << std::endl;
    if (aspiration_active)
        std::cout << "c Algorithmic: aspiration_active = true" << std::endl;
    else
        std::cout << "c Algorithmic: aspiration_active = false" << std::endl;
}

void print_solution()
{
    int i;

    std::cout << "v ";
    for (i = 1; i <= num_vars; i++)
    {
        if (cur_soln[i] == 0)
            std::cout << "-";
        std::cout << i;
        if (i % 10 == 0)
            std::cout << std::endl
                      << "v ";
        else
            std::cout << ' ';
    }
    std::cout << "0" << std::endl;

#if defined USE_INIT_PREDICT
    int sumcorr = 0;
    for (i = 1; i <= num_vars; i++)
    {
        if (cur_soln[i] == cnf_predict.output[i - 1])
            sumcorr += 1;
    }
    double div = (double)sumcorr / num_vars;
    std::cout << "c samerate " << div << std::endl;
    std::cout << "c predict time" << predict_time;
#endif // USE_INIT_PREDICT
}

int verify_sol()
{
    int c, j;
    int flag;

    if (simplify == 0)
    {

        for (c = 0; c < num_clauses; ++c)
        {
            flag = 0;
            for (j = 0; j < clause_lit_count[c]; ++j)
                if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
                {
                    flag = 1;
                    break;
                }

            if (flag == 0)
            { //output the clause unsatisfied by the solution
                std::cout << "c clause " << c << " is not satisfied" << std::endl;

                std::cout << "c ";
                for (j = 0; j < clause_lit_count[c]; ++j)
                {
                    if (clause_lit[c][j].sense == 0)
                        std::cout << "-";
                    std::cout << clause_lit[c][j].var_num << " ";
                }
                std::cout << std::endl;

                for (j = 0; j < clause_lit_count[c]; ++j)
                    std::cout << cur_soln[clause_lit[c][j].var_num] << " ";
                std::cout << std::endl;

                return 0;
            }
        }
    }

    if (simplify == 1)
    {
        for (c = 0; c < num_clauses; ++c)
        {
            flag = 0;
            for (j = 0; j < org_clause_lit_count[c]; ++j)
                if (cur_soln[org_clause_lit[c][j].var_num] == org_clause_lit[c][j].sense)
                {
                    flag = 1;
                    break;
                }

            if (flag == 0)
            { //output the clause unsatisfied by the solution
                std::cout << "c clause " << c << " is not satisfied" << std::endl;

                if (clause_delete[c] == 1)
                    std::cout << "c this clause is deleted by UP." << std::endl;

                std::cout << "c ";
                for (j = 0; j < org_clause_lit_count[c]; ++j)
                {
                    if (org_clause_lit[c][j].sense == 0)
                        std::cout << "-";
                    std::cout << org_clause_lit[c][j].var_num << " ";
                }
                std::cout << std::endl;

                for (j = 0; j < org_clause_lit_count[c]; ++j)
                    std::cout << cur_soln[org_clause_lit[c][j].var_num] << " ";
                std::cout << std::endl;

                return 0;
            }
        }
    }

    return 1;
}
