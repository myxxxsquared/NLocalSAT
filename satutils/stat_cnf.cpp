
#include <string>
#include <fstream>
#include <map>
#include <tuple>
#include <stdio.h>

#include <boost/python/tuple.hpp>
#include <boost/python/dict.hpp>

#include "ScopedGILRelease.hpp"

boost::python::tuple stat_cnf(std::string filename)
{
    std::map<int, int> num_clause_len;
    int total_len=0, max_len=0;
    int num_vars, num_clauses;
    {
        ScopedGILRelease gil;

        FILE *ifs = fopen(filename.c_str(), "r");
        char buffer[10240];

        while (fgets(buffer, sizeof(buffer), ifs))
        {
            if (buffer[0] == 'p')
            {
                sscanf(buffer, "p cnf %d %d", &num_vars, &num_clauses);
                break;
            }
        }

        int cur_clause_len = 0;
        int cur_lit;
        while (fscanf(ifs, "%d", &cur_lit) == 1)
        {
            if (cur_lit != 0)
                cur_clause_len += 1;
            if (cur_lit == 0)
            {
                if(cur_clause_len > max_len)
                    max_len = cur_clause_len;
                total_len += cur_clause_len;
                auto it = num_clause_len.find(cur_clause_len);
                if (it == num_clause_len.end())
                    num_clause_len.insert(std::make_pair(cur_clause_len, 1));
                else
                    it->second += 1;
                cur_clause_len = 0;
            }
        }

        fclose(ifs);
    }

    boost::python::dict dict;
    for (auto item : num_clause_len)
        dict[item.first] = item.second;
    return boost::python::make_tuple(num_vars, num_clauses, max_len, total_len, dict);
}
