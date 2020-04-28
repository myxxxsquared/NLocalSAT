/*
Copyright 2018 Wenjie Zhang (wenjiez696@gmail.com)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include "batchgenerator.hpp"
#include "py_utils.hpp"
#include "satassert.hpp"
#include <algorithm>

namespace sat
{

PyObject *Wrap_PyArray_SimpleNew(int nd, npy_intp *dims, int typenum)
{
    PyObject *result = PyArray_SimpleNew(nd, dims, typenum);
    if (!result)
        throw std::runtime_error("PyArray_SimpleNew failed.");
    return result;
}

BatchGenerator::BatchGenerator()
    : edges(), labels(), num_vars(0), num_clauses(0)
{
}

bool BatchGenerator::append(const Problem &problem, int verbose)
{
    auto space_all = problem.solution_space();
    auto &space = space_all.first;
    if(!space_all.second)
        return false;

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

    if(verbose)
        fprintf(stderr, "gen v: %d; c: %d\n", num_vars, num_clauses);

    for (auto &c : space)
    {
        double a = c.first, b = c.second;
        double s = a / (a + b);

        int lab;

        if (s < 0.5)
            lab = 0;
        else
            lab = 1;

        // if( s < 0.001 )
        //     lab = 0;
        // else if(s < 0.5)
        //     lab = 1;
        // // else if(s < 0.5)
        // //     lab = 2;
        // // else if(s <= 0.9)
        // //     lab = 3;
        // else if(s <= 0.999)
        //     lab = 4;
        // else
        //     lab = 5;

        this->labels.push_back(lab);
    }

    sat_assert_debug(num_vars == (int)(labels.size()));

    return true;
}

PyObject *BatchGenerator::py_labels() const
{
    // npy_intp sizes[] = {this->num_vars, 6};
    // PyObject *r = Wrap_PyArray_SimpleNew(2, sizes, NPY_FLOAT32);
    // float *data = (float *)PyArray_DATA((PyArrayObject *)r);
    // for (int i = 0; i < this->num_vars; ++i)
    //     for(int j = 0; j < 6; ++j)
    //         data[6*i + j] = this->labels[i] == j ? 1.0f : 0.0f;
    // return r;

    npy_intp sizes[] = {this->num_vars};
    PyObject *r = Wrap_PyArray_SimpleNew(1, sizes, NPY_INT64);
    long *data = (long *)PyArray_DATA((PyArrayObject *)r);
    for (int i = 0; i < this->num_vars; ++i)
        data[i] = this->labels[i];
    return r;
}

PyObject *BatchGenerator::py_edges() const
{
    npy_intp sizes_i[] = {(npy_intp)edges.size(), 2};
    PyObject *indices = Wrap_PyArray_SimpleNew(2, sizes_i, NPY_INT32);
    int *data_i = (int *)PyArray_DATA((PyArrayObject *)indices);

    for (int i = 0; i < (int)edges.size(); ++i)
    {
        auto &item = edges[i];
        data_i[2 * i] = std::get<0>(item);
        data_i[2 * i + 1] = std::get<2>(item) ? std::get<1>(item) : std::get<1>(item) + num_vars;
    }

    return indices;
}

PyObject *BatchGenerator::to_python() const
{
    PyObject *result = PyTuple_New(4);
    PyTuple_SetItem(result, 0, PyLong_FromLong(this->num_vars));
    PyTuple_SetItem(result, 1, PyLong_FromLong(this->num_clauses));
    PyTuple_SetItem(result, 2, this->py_labels());
    PyTuple_SetItem(result, 3, this->py_edges());
    return result;
}
}
