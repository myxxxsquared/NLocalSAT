
#include "problem.hpp"
#include "satassert.hpp"

#include <list>
#include <deque>
#include <stdexcept>

namespace sat
{
void Problem::generate_clauses(int num_clauses, float p_three, sat_random_engine &engine)
{
    sat_assert(this->num_vars >= 3);
    sat_assert(num_clauses > 0);
    sat_assert(p_three >= 0 && p_three <= 1);

    std::uniform_real_distribution<> rdist;
    std::uniform_int_distribution<> idist{0, this->num_vars - 1};
    std::uniform_int_distribution<> ndist{0, 1};

    sat_problem.clear();
    sat_problem.resize(num_clauses);
    for (int i = 0; i < num_clauses; ++i)
    {
        auto &clause = this->sat_problem[i];
        int clause_len = rdist(engine) < p_three ? 3 : 2;
        clause.reserve(clause_len);
        for (int j = 0; j < clause_len; ++j)
        {
            int newval;
            bool cont = true;
            while (cont)
            {
                newval = idist(engine);
                cont = false;
                for (Lit oldval : clause)
                    if (oldval.index() == newval)
                        cont = true;
            }
            clause.push_back(Lit(newval, ndist(engine) == 0));
        }
    }
}

bool Problem::assign(const Assign &val) const
{
    sat_assert((int)val.value.size() == this->num_vars);

    for (auto &clause : this->sat_problem)
    {
        bool sat = false;
        for (auto &lit : clause)
        {
            sat_assert_debug(lit.index() >= 0 && lit.index() < this->num_vars);
            if (!((bool)val.value[lit.index()] ^ (bool)lit.sign()))
            {
                sat = true;
                break;
            }
        }
        if (!sat)
            return false;
    }
    return true;
}

struct solve_info
{
    std::list<std::list<Lit>> clauses;
    std::vector<std::pair<int, int>> occour;
    std::vector<bool> assigned, assignment;
    int num_vars, var_assigned;
    bool sat, unsat;

    void init(const Problem &problem)
    {
        var_assigned = 0;
        num_vars = problem.num_vars;

        clauses.clear();
        occour.clear();
        assigned.clear();
        assignment.clear();

        assigned.resize(num_vars, false);
        assignment.resize(num_vars);
        occour.resize(num_vars, std::make_pair(0, 0));

        sat = unsat = false;

        for (auto &c : problem.sat_problem)
        {
            clauses.emplace_back();
            auto &back = clauses.back();
            for (auto &l : c)
            {
                auto &o = occour[l.index()];
                if (l.sign())
                    ++o.first;
                else
                    ++o.second;
                back.push_back(l);
            }
        }
    }

    void spread(Lit l)
    {
        std::deque<Lit> spreadlist;
        spreadlist.push_back(l);

        while (!spreadlist.empty())
        {
            spread(spreadlist.front(), spreadlist);
            spreadlist.pop_front();
            if (sat || unsat)
            {
                return;
            }
        }
    }

    void spread(Lit l, std::deque<Lit> &queue)
    {
        // check if the variable is assigned
        if (assigned[l.index()])
        {
            if (assignment[l.index()] == l.sign())
            {
                return;
            }
            else
            {
                unsat = true;
                return;
            }
        }

        var_assigned++;
        assigned[l.index()] = true;
        assignment[l.index()] = l.sign();

        // check all caluse
        for (auto it = clauses.begin(); it != clauses.end();)
        {
            bool to_remove = false;
            for (auto it2 = it->begin(); it2 != it->end();)
            {
                if (it2->index() == l.index())
                {
                    if (it2->sign() == l.sign())
                    {
                        to_remove = true;
                        break;
                    }
                    else
                    {
                        auto &c = occour[it2->index()];
                        if (it2->sign())
                            --c.first;
                        else
                            --c.second;
                        it2 = it->erase(it2);
                        continue;
                    }
                }
                ++it2;
            }
            if (to_remove)
            {
                for (auto &l : *it)
                {
                    auto &c = occour[l.index()];
                    if (l.sign())
                        --c.first;
                    else
                        --c.second;
                }
                it = clauses.erase(it);
                continue;
            }
            if (it->size() == 0)
            {
                unsat = true;
                return;
            }
            if (it->size() == 1)
            {
                queue.push_back(*it->begin());
            }
            ++it;
        }

        if (clauses.size() == 0)
        {
            sat = true;
            return;
        }
    }

    void solve_space(std::vector<std::pair<double, double>> &result, bool &can_sat)
    {
        if (unsat)
            return;
        if (sat)
        {
            can_sat = true;

            int var_unassigned = num_vars - var_assigned;
            double var_unassigned_d = pow(2, var_unassigned);
            for (int i = 0; i < num_vars; ++i)
            {
                if (assigned[i])
                {
                    if (assignment[i])
                        result[i].first += var_unassigned_d;
                    else
                        result[i].second += var_unassigned_d;
                }
                else
                {
                    result[i].first += var_unassigned_d / 2;
                    result[i].second += var_unassigned_d / 2;
                }
            }
            return;
        }

        int maxindex = 0, maxref = 0;
        for (int i = 0; i < num_vars; ++i)
        {
            if (assigned[i])
                continue;
            if (occour[i].first + occour[i].second > maxref)
            {
                maxref = occour[i].first + occour[i].second;
                maxindex = i;
            }
        }

        {
            auto cpy_pos = *this;
            cpy_pos.spread(Lit(maxindex, true));
            cpy_pos.solve_space(result, can_sat);
        }

        {
            auto cpy_pos = *this;
            cpy_pos.spread(Lit(maxindex, false));
            cpy_pos.solve_space(result, can_sat);
        }
    }
};

std::pair<std::vector<std::pair<double, double>>, bool> Problem::solution_space() const
{
    std::vector<std::pair<double, double>> result;
    result.resize(this->num_vars, std::make_pair(0, 0));
    bool sat = false;

    solve_info info;
    info.init(*this);
    info.solve_space(result, sat);

    return std::make_pair(result, sat);
}

void Problem::save(const char *filename)
{
    FILE *outputfile = fopen(filename, "w");
    if (NULL == outputfile)
        throw std::runtime_error("Cannot open file");

    fprintf(outputfile, "c generated by https://github.com/myxxxsquared/sat\n");
    fprintf(outputfile, "p cnf %d %d\n", num_vars, num_clauses());

    for (auto &clause : sat_problem)
    {
        for (auto &lit : clause)
            fprintf(outputfile, "%d ", lit.sign() ? (lit.index() + 1) : -(lit.index() + 1));
        fprintf(outputfile, "0\n");
    }

    fclose(outputfile);
}
} // namespace sat
