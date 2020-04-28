
#ifndef SAT_PROBLEM_HEADER
#define SAT_PROBLEM_HEADER

#include "lit.hpp"
#include "rand.hpp"
#include "assign.hpp"
#include <vector>
#include <utility>

namespace sat
{
class Problem
{
public:
    inline Problem(int n_vars) : sat_problem(), num_vars(n_vars) {}
    std::vector<std::vector<Lit>> sat_problem;
    int num_vars;
    void generate_clauses(int num_clauses, float p_three, sat_random_engine &engine);
    bool assign(const Assign &val) const;
    std::pair<std::vector<std::pair<double, double>>, bool> solution_space() const;
    inline int num_clauses() const { return (int)sat_problem.size(); }
    void save(const char *filename);
};
} // namespace sat

#endif
