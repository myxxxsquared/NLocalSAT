
#include "satbasic.hpp"

#include "predict.hpp"
#include <stdexcept>
#include <stdio.h>

int run_solver(int argc, char *argv[]);

int innermain(int argc, char *argv[])
{
    run_solver(argc, argv);
    return 0;
}

int main(int argc, char *argv[])
{
    try
    {
        return innermain(argc, argv);
    }
    catch (std::runtime_error ex)
    {
        fprintf(stderr, "ERROR: %s\n", ex.what());
        return -1;
    }
}
