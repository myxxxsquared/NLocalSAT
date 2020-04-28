
#include "satbasic.hpp"

#include <iostream>
#include <signal.h>
#include <unistd.h>

static void siginthandler(int)
{
    times(&time_stop);
    double comp_time = double(time_stop.tms_utime - time_start.tms_utime) / sysconf(_SC_CLK_TCK);

    std::cout << std::endl
              << "SIGINT RECEIVED" << std::endl;
    std::cout << "c solveSteps = " << tries << " tries + " << step << " steps (each try has " << max_flips << " steps)." << std::endl;
    std::cout << "c solveTime = " << comp_time << std::endl;

    exit(1);
}

void initsigint()
{
    signal(SIGINT, siginthandler);
}
