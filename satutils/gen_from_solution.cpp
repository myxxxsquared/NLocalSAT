
#include <algorithm>
#include <stdexcept>
#include <tuple>
#include <set>
#include <map>
#include <random>

#include "AutoCloseFile.hpp"
#include "gen_from_solution.hpp"
#include "ScopedGILRelease.hpp"

std::vector<Problem> Problem::split(int eachlen)
{
    ScopedGILRelease gil;
    std::vector<int> maps;
    std::vector<bool> neg;
    maps.resize(num_vars);
    for (int i = 0; i < num_vars; ++i)
        maps[i] = i;
    neg.resize(num_vars);

    auto engine = std::default_random_engine();
    std::uniform_int_distribution<int> dist{0, 1};
    std::shuffle(maps.begin(), maps.end(), engine);
    std::generate(neg.begin(), neg.end(), [&engine, &dist] { return dist(engine); });

    std::vector<Problem> problems;
    int numproblems = (num_vars - 1) / eachlen + 1;
    problems.resize(numproblems);

    for (int i = 0; i < numproblems; ++i)
    {
        problems[i].num_vars = std::min(eachlen, num_vars - eachlen * i);
        problems[i].sat_solution.resize(problems[i].num_vars);
    }

    for (int i = 0; i < num_vars; ++i)
    {
        bool isneg = neg[i];
        int cur_index_range = maps[i] / eachlen;
        int cur_index = maps[i] - eachlen * cur_index_range;
        if (cur_index < 0 || cur_index >= (int)problems[cur_index_range].sat_solution.size())
            *(int *)0 = 0;
        problems[cur_index_range].sat_solution[cur_index] = sat_solution[i] ^ isneg;
    }

    for (int i = 0; i < numproblems; ++i)
        if (problems[i].num_vars != (int)problems[i].sat_solution.size())
            *(int *)0 = 0;

    for (auto &clause : sat_problem)
    {
        std::vector<Lit> cur_clause;
        std::set<int> in_range;

        for (auto &cur_lit : clause)
            if (sat_solution[cur_lit.index()] == cur_lit.sign())
                in_range.insert(maps[cur_lit.index()] / eachlen);

        std::map<int, std::vector<Lit>> clause_maps;
        for (int partial : in_range)
            clause_maps.insert(std::make_pair(partial, std::vector<Lit>()));

        for (auto &cur_lit : clause)
        {
            bool isneg = neg[cur_lit.index()];
            int cur_index = maps[cur_lit.index()];
            int cur_index_range = cur_index / eachlen;
            if (in_range.find(cur_index_range) == in_range.end())
                continue;
            if (cur_index_range < 0 || cur_index_range > numproblems)
                *(int *)0 = 0;
            cur_index = cur_index - cur_index_range * eachlen;
            if (cur_index < 0 || cur_index >= problems[cur_index_range].num_vars)
                *(int *)0 = 0;
            clause_maps[cur_index_range].push_back(Lit(cur_index, cur_lit.sign() ^ isneg));
        }

        for (auto &m : clause_maps)
            if (m.second.size() >= 2)
                problems[m.first].sat_problem.push_back(std::move(m.second));
    }

    return problems;
}

void Problem::load(const char *filename)
{
    ScopedGILRelease gil;

    num_vars = -1;
    sat_problem.clear();

    int cur_num_clauses;
    AutoCloseFile ifs{fopen(filename, "r")};
    if (NULL == (FILE *)ifs)
        throw sat_bad_file("fail to open");
    char buffer[10240];

    while (fgets(buffer, sizeof(buffer), ifs))
    {
        if (buffer[0] == 'p')
        {
            sscanf(buffer, "p cnf %d %d", &num_vars, &cur_num_clauses);
            break;
        }
    }

    if (num_vars == -1)
        throw sat_bad_format("no 'p cnf'");

    int cur_lit;
    std::vector<Lit> curclause;
    while (fscanf(ifs, "%d", &cur_lit) == 1)
    {
        if (cur_lit != 0)
        {
            Lit l = Lit::fromvalue(cur_lit);
            if (l.index() >= num_vars)
                throw sat_bad_format("invaild index");
            curclause.push_back(l);
        }
        if (cur_lit == 0)
        {
            if (curclause.size() == 0)
                throw sat_bad_format("zero length clause");
            sat_problem.push_back(std::move(curclause));
            curclause.clear();
        }
    }

    if (cur_num_clauses != get_num_clauses())
    {
        throw sat_bad_format("num clause doesn't match");
    }
}

void Problem::load_solution(const char *filename)
{
    ScopedGILRelease gil;

    AutoCloseFile ifs{fopen(filename, "r")};
    if (NULL == (FILE *)ifs)
        throw sat_bad_file("Cannot open file");
    for (int first; (first = fgetc(ifs)) != EOF;)
    {
        if (first != 'v')
        {
            if (first != '\n')
                (void)(1 + fscanf(ifs, "%*[^\n]\n"));
            continue;
        }
        sat_solution.resize(num_vars, false);
        for (int cur_solution; fscanf(ifs, "%d", &cur_solution) == 1;)
        {
            Lit l = Lit::fromvalue(cur_solution);
            if (l.index() >= num_vars)
                throw sat_bad_format("index error");
            sat_solution[l.index()] = (int)l.sign();
        }
        return;
    }
    throw sat_no_solution("no solution");
}

void Problem::save(const char *filename) const
{
    ScopedGILRelease gil;
    AutoCloseFile outputfile{fopen(filename, "w")};
    if (NULL == (FILE *)outputfile)
        throw std::runtime_error("Cannot open file");

    fprintf(outputfile, "c generated by https://github.com/myxxxsquared/sat\n");
    fprintf(outputfile, "p cnf %d %d\n", num_vars, get_num_clauses());

    for (auto &clause : sat_problem)
    {
        for (auto &lit : clause)
            fprintf(outputfile, "%d ", lit.sign() ? (lit.index() + 1) : -(lit.index() + 1));
        fprintf(outputfile, "0\n");
    }
}

BatchGenerator::BatchGenerator()
    : edges(), labels(), num_vars(0), num_clauses(0)
{
}

bool BatchGenerator::append(const Problem &problem, int verbose)
{
    ScopedGILRelease gil;
    for (int i = 0; i < (int)problem.sat_problem.size(); ++i)
    {
        auto &clause = problem.sat_problem[i];
        for (const Lit &l : clause)
        {
            edges.push_back(std::make_tuple(
                i + num_clauses,
                l.index() + num_vars,
                (int)l.sign()));
        }
    }

    num_clauses += (int)problem.sat_problem.size();
    num_vars += problem.num_vars;

    if (verbose)
        fprintf(stderr, "gen v: %d; c: %d\n", num_vars, num_clauses);

    this->labels.insert(this->labels.end(), problem.sat_solution.begin(), problem.sat_solution.end());

    if ((int)this->labels.size() != num_vars)
        *(int *)0 = 0;

    return true;
}

#include <boost/python/object.hpp>
#include <boost/python/tuple.hpp>
#include <boost/python/numpy.hpp>

namespace p = boost::python;
namespace np = boost::python::numpy;

void init_boost_numpy()
{
    np::initialize();
}

boost::python::object BatchGenerator::save()
{
    auto labels = np::empty(p::make_tuple(n_vars()), np::dtype::get_builtin<long>());
    auto edges = np::empty(p::make_tuple(n_lits(), 2), np::dtype::get_builtin<int>());

    auto labels_data = reinterpret_cast<long *>(labels.get_data());
    for (int i = 0; i < (int)this->labels.size(); ++i)
        labels_data[i] = (int)this->labels[i];

    auto edges_data = reinterpret_cast<int *>(edges.get_data());
    for (int i = 0; i < (int)this->n_lits(); ++i)
    {
        auto &item = this->edges[i];
        edges_data[2 * i] = std::get<0>(item);
        edges_data[2 * i + 1] = std::get<2>(item) ? std::get<1>(item) : std::get<1>(item) + num_vars;
    }

    return p::make_tuple(n_vars(), n_clauses(), labels, edges);
}

boost::python::object Problem::to_data() const
{
    int num_lits = 0;
    for (auto &clause : sat_problem)
        num_lits += clause.size();
    auto edges = np::empty(p::make_tuple(num_lits, 2), np::dtype::get_builtin<int>());
    auto edges_data = reinterpret_cast<int *>(edges.get_data());
    // int s0 = edges.strides(0);
    // int s1 = edges.strides(1);
    // if (s0 != 8 || s1 != 4)
    //     *(int *)0 = 0;

    int curloc = 0;
    for (int i = 0; i < (int)sat_problem.size(); ++i)
    {
        auto &clause = sat_problem[i];
        for (auto l : clause)
        {
            edges_data[2 * curloc] = i;
            edges_data[2 * curloc + 1] = l.sign() ? l.index() : l.index() + num_vars;
            // if (edges_data[2 * curloc] < 0 || edges_data[2 * curloc] >= (int)sat_problem.size() || edges_data[2 * curloc + 1] < 0 || edges_data[2 * curloc + 1] >= 2 * num_vars)
            //     *(int *)0 = 0;
            curloc += 1;
        }
    }
    if (curloc != num_lits)
        *(int *)0 = 0;
    return p::make_tuple(num_vars, sat_problem.size(), edges);
}
