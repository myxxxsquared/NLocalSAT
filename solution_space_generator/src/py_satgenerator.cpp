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

#define MYLIBRARY_USE_IMPORT
#include "py_utils.hpp"
#include "rand.hpp"
#include "batchgenerator.hpp"
#include "problem.hpp"

#include <stdexcept>

struct generate_config
{
    int num_total, num_each_min, num_each_max;
    float rate_clauses_min, rate_clauses_max;
    float rate_three;
    int runid;
    int verbose;
};

PyObject *generate_data(generate_config &config)
{
    // fprintf(stderr, "generate_data.\n");
    sat::BatchGenerator batchgenerator;
    {
        PyAllowThreads allowthreads;

        sat::sat_random_engine engine{config.runid};
        std::uniform_int_distribution<> idist{config.num_each_min, config.num_each_max};
        std::uniform_real_distribution<> fdist{config.rate_clauses_min, config.rate_clauses_max};

        while (batchgenerator.n_vars() < config.num_total)
        {
            // fprintf(stderr, "DEBUG: %d\n", batchgenerator.n_vars());
            int numv = idist(engine);
            int numc = (int)(fdist(engine) * numv);

            // fprintf(stderr, "generate_problem: %d, %d, %d.\n", numv, numc, batchgenerator.num_nodes());
            while(true)
            {
                sat::Problem gen{numv};
                gen.generate_clauses(numc, config.rate_three, engine);
                if(batchgenerator.append(gen, config.verbose))
                    break;
            }
        }
    }

    return batchgenerator.to_python();
}

PyObject *py_generate_data(PyObject *, PyObject *args, PyObject *keywords)
{
    static char name_num_total[] = "num_total";
    static char name_num_each_min[] = "num_each_min";
    static char name_num_each_max[] = "num_each_max";
    static char name_num_clauses_min[] = "rate_clauses_min";
    static char name_num_clauses_max[] = "rate_clauses_max";
    static char name_three_rate[] = "rate_three";
    static char name_run_id[] = "run_id";
    static char name_verbose[] = "verbose";
    static char *kwlist[] = {name_num_total, name_num_each_min, name_num_each_max, name_num_clauses_min, name_num_clauses_max, name_three_rate, name_run_id, name_verbose, NULL};

    generate_config config;

    if (!PyArg_ParseTupleAndKeywords(args, keywords, "iiifffip", kwlist,
                                     &config.num_total, &config.num_each_min, &config.num_each_max,
                                     &config.rate_clauses_min, &config.rate_clauses_max, &config.rate_three,
                                     &config.runid, &config.verbose))
        return NULL;

    try
    {
        return generate_data(config);
    }
    catch (std::runtime_error err)
    {
        PyErr_SetString(PyExc_RuntimeError, err.what());
        return NULL;
    }
}

static PyMethodDef methods[] = {
    {"_generate_data", (PyCFunction)py_generate_data, METH_VARARGS | METH_KEYWORDS, NULL},
    {NULL, NULL, 0, NULL}};

static struct PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "_satgenerator",
    NULL,
    -1,
    methods};

PyMODINIT_FUNC
PyInit__satgenerator(void)
{
    import_array();
    return PyModule_Create(&module);
}
