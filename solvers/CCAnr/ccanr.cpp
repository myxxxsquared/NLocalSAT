

#include <time.h>
#include <unistd.h>
#include <iostream>
#include <signal.h>
#include <stdlib.h>

#include "satbasic.hpp"

int run_solver(int argc, char *argv[])
{
    int satisfy_flag = 0;

    bool ret = parse_arguments(argc, argv);
    if (!ret)
    {
        std::cout << "Arguments Error!" << std::endl;
        return -1;
    }

    srand(seed);

#ifdef USE_PREDICT
    run_predict();
#endif // USE_PREDICT

    times(&time_start);

    if (!load())
    {
        std::cout << "Load Failed!" << std::endl;
        return -1;
    }

    print_information();

    step = 0;
    tries = 0;

    initsigint();

    for (; tries <= max_tries; tries++)
    {
        local_search(ls_no_improv_times);

        if (unsat_stack_fill_pointer == 0)
        {
            if (verify_sol() == 1)
            {
                satisfy_flag = 1;
                break;
            }
            else
                std::cout << "c Sorry, something is wrong." << std::endl;
        }
    }

    times(&time_stop);
    double comp_time = double(time_stop.tms_utime - time_start.tms_utime) / sysconf(_SC_CLK_TCK);

    if (satisfy_flag == 1)
    {
        std::cout << "s SATISFIABLE" << std::endl;
        print_solution();
    }
    else
        std::cout << "s UNKNOWN" << std::endl;

    std::cout << "c solveSteps = " << tries << " tries + " << step << " steps (each try has " << max_flips << " steps)." << std::endl;
    std::cout << "c solveTime = " << comp_time << std::endl;

    free_memory();

    return 0;
}
