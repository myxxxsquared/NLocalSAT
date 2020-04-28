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

#ifndef SAT_BATCHGENERATOR_HEADER
#define SAT_BATCHGENERATOR_HEADER

#include <vector>
#include <tuple>
#include <Python.h>

#include "problem.hpp"

namespace sat
{

class BatchGenerator
{
    std::vector<std::tuple<int, int, int>> edges;
    std::vector<int> labels;

    int num_vars, num_clauses;

    PyObject *py_labels() const;
    PyObject *py_edges() const;

  public:
    BatchGenerator();
    bool append(const Problem &problem, int verbose = 0);
    /// ( num_nodes, num_clauses, labels, weights, (edges1_indices, edges1_values), (edges2_indices, edges2_values) )
    PyObject *to_python() const;
    inline int n_vars() const { return num_vars; }
};
}
#endif
