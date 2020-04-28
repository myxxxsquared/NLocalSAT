
#include "problem.hpp"

int main(int argc, char *argv[])
{
    // 0        1        2    3    4         5    6
    // genrator num_vars rmin rmax num_three seed output

    sat::sat_random_engine engine{(long unsigned int)atoi(argv[5])};
    std::uniform_real_distribution<> fdist{atof(argv[2]), atof(argv[3])};

    int numv, numc;
    float three;
    numv = atoi(argv[1]);
    numc = (int)(fdist(engine) * numv);
    three = atof(argv[4]);

    sat::Problem problem{numv};
    problem.generate_clauses(numc, three, engine);
    problem.save(argv[6]);
    return 0;
}
