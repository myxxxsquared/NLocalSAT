
#include <boost/python.hpp>
#include <string>
#include <cstdio>
#include <random>
#include <boost/lexical_cast.hpp>
#include <boost/format.hpp>

#include "ScopedGILRelease.hpp"
#include "AutoCloseFile.hpp"

typedef std::vector<std::vector<int>> sat_problem;

void split_cnf(std::string input_file, std::string output_fileprefix, int eachlen, int randomseed, double minsize, bool multisplit)
{
    ScopedGILRelease gil;
    int num_vars = -1, num_clauses = -1;
    AutoCloseFile ifs{fopen(input_file.c_str(), "r")};
    char buffer[10240];

    while (fgets(buffer, sizeof(buffer), ifs))
    {
        if (buffer[0] == 'p')
        {
            sscanf(buffer, "p cnf %d %d", &num_vars, &num_clauses);
            break;
        }
    }

    if (num_vars <= 0 || num_clauses <= 0)
        return;

    std::vector<std::vector<int>> clauses;
    clauses.emplace_back();
    for (int cur_lit; fscanf(ifs, "%d", &cur_lit) == 1;)
    {
        if (cur_lit != 0)
        {
            clauses.back().emplace_back(cur_lit);
        }
        else
        {
            clauses.emplace_back();
        }
    }
    clauses.pop_back();

    int times = /* num_vars / eachlen;
    if (times == 0)
        times = 1;
    if (!multisplit)
        times = */ 1;

    int outputid = 0;

    for (int thist = 0; thist < times; ++thist)
    {
        std::vector<int> maps;
        maps.resize(num_vars);
        for (int i = 0; i < num_vars; ++i)
            maps[i] = i;
        std::shuffle(maps.begin(), maps.end(), std::default_random_engine(randomseed));

        std::vector<sat_problem> problems;
        int numproblems = (num_vars - 1) / eachlen + 1;
        problems.resize(numproblems);

        for (auto &clause : clauses)
        {
            int cur_range = -1;
            bool vaild = true;
            std::vector<int> cur_clause;

            for (auto cur_lit : clause)
            {
                bool cur_sign = cur_lit > 0;
                int cur_index = cur_sign ? cur_lit - 1 : -cur_lit - 1;
                cur_index = maps[cur_index];
                int cur_index_range = cur_index / eachlen;
                if (cur_index_range < 0 || cur_index_range > numproblems)
                    *(int *)0 = 0;
                if (cur_range == -1 || cur_index_range == cur_range)
                {
                    cur_range = cur_index_range;
                    cur_index = cur_index - cur_range * eachlen;
                    cur_clause.push_back(cur_sign ? cur_index + 1 : -(cur_index + 1));
                }
                else
                {
                    vaild = false;
                    cur_clause.clear();
                }
            }

            if (vaild)
            {
                problems[cur_range].push_back(std::move(cur_clause));
            }
        }

        for (int i = 0; i < numproblems; ++i)
        {
            sat_problem &problem = problems[i];
            int cur_size = std::min(eachlen, num_vars - i * eachlen);
            if ((double)problem.size() >= (double)cur_size * minsize)
            {
                // printf("num_vars: %d\n", num_vars);
                std::string output_file_name = (boost::format("%1%%2$04d.cnf") % output_fileprefix % outputid++).str();
                AutoCloseFile foutput{fopen(output_file_name.c_str(), "w")};
                fprintf(foutput, "p cnf %d %d\n", cur_size, (int)problem.size());
                for (auto &clause : problem)
                {
                    for (int lit : clause)
                        fprintf(foutput, "%d ", lit);
                    fprintf(foutput, "0\n");
                }
            }
        }
    }
}