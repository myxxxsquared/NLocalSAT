
#include "satbasic.hpp"

#ifdef USE_PREDICT

#include <stdexcept>
#include <fstream>
#include <vector>
#include "predict.hpp"

#define MYLIBRARY_USE_IMPORT
#include "py_utils.hpp"

namespace sat_predict
{

PyObject *Wrap_PyArray_SimpleNew(int nd, npy_intp *dims, int typenum)
{
    PyObject *result = PyArray_SimpleNew(nd, dims, typenum);
    if (!result)
        throw std::runtime_error("PyArray_SimpleNew failed.");
    return result;
}

SATPredict::SATPredict(const char *gpu, const char *load_model)
{
    PyObject *module_satpredict = NULL, *class_satpredict = NULL, *init_args = NULL;
    this->satpredict = NULL;

    try
    {
        module_satpredict = PyImport_ImportModule("sat_predict");
        if (module_satpredict == NULL)
        {
            PyErr_Print();
            throw std::runtime_error("PyImport_ImportModule(\"sat_predict\")");
        }
        class_satpredict = PyObject_GetAttrString(module_satpredict, "SATPredict");
        if (class_satpredict == NULL)
        {
            PyErr_Print();
            throw std::runtime_error("PyObject_GetAttrString(module_satpredict, \"SATPredict\")");
        }

        init_args = PyTuple_New(2);
        if (init_args == NULL)
        {
            PyErr_Print();
            throw std::runtime_error("PyTuple_New(1)");
        }
        // PyTuple_SetItem(init_args, 0, PyUnicode_FromString(filename));
        PyTuple_SetItem(init_args, 0, PyUnicode_FromString(gpu));
        PyTuple_SetItem(init_args, 1, PyUnicode_FromString(load_model));
        this->satpredict = PyObject_CallObject(class_satpredict, init_args);
        if (this->satpredict == NULL)
        {
            PyErr_Print();
            throw std::runtime_error("PyObject_CallObject(class_satpredict, init_args)");
        }
    }
    catch (std::runtime_error err)
    {
        Py_XDECREF(module_satpredict);
        Py_XDECREF(init_args);
        Py_XDECREF(this->satpredict);
        throw err;
    }
    Py_XDECREF(module_satpredict);
    Py_XDECREF(init_args);
}

SATPredict::~SATPredict()
{
    Py_XDECREF(this->satpredict);
}

void SATPredict::predict(int num_vars, int num_clauses, int num_edges, const int edges[][2], int output[])
{
    // generate numpy array
    npy_intp sizes_i[] = {(npy_intp)num_edges, 2};
    PyObject *indices = Wrap_PyArray_SimpleNew(2, sizes_i, NPY_INT32);
    {
        int *data_i = (int *)PyArray_DATA((PyArrayObject *)indices);
        const int *data_j = (int *)edges;
        int datalength = num_edges * 2;
        for (int i = 0; i < datalength; ++i)
            *(data_i++) = *(data_j++);
    }

    // generate args
    PyObject *args = NULL;
    args = PyTuple_New(3);
    if (NULL == args)
    {
        PyErr_Print();
        Py_XDECREF(indices);
        throw std::runtime_error("PyTuple_New(3)");
    }
    PyTuple_SetItem(args, 0, PyLong_FromLong(num_vars));
    PyTuple_SetItem(args, 1, PyLong_FromLong(num_clauses));
    PyTuple_SetItem(args, 2, indices);

    // call predict
    PyObject *result = NULL;
    result = PyObject_CallObject(this->satpredict, args);
    Py_XDECREF(args);
    if (NULL == result)
    {
        PyErr_Print();
        throw std::runtime_error("PyObject_CallObject(this->satpredict, args)");
    }

    // check result
    if (!PyArray_Check(result) || !(PyArray_NDIM((PyArrayObject *)result) == 1) || !(PyArray_DIMS((PyArrayObject *)result)[0] == num_vars) || !(PyArray_DESCR((PyArrayObject *)result)->type_num == NPY_INT32))
    {
        Py_XDECREF(result);
        throw std::runtime_error("check failed.");
    }

    // parse result
    int *resultarray = (int *)PyArray_DATA((PyArrayObject *)result);
    for (int i = 0; i < num_vars; ++i)
        output[i] = resultarray[i];

    Py_XDECREF(result);
}
} // namespace sat_predict

bool run_predict()
{
    cnf_predict.num_clauses = -1;
    cnf_predict.num_edges = -1;
    cnf_predict.num_vars = -1;
    cnf_predict.edges = NULL;
    cnf_predict.output = NULL;

    if (predictfile.empty())
    {
        std::ifstream ifs{inst.c_str()};
        if (!ifs)
            return false;
        std::string line;
        std::getline(ifs, line);
        while (line[0] != 'p')
            std::getline(ifs, line);

        sscanf(line.c_str(), "p cnf %d %d", &cnf_predict.num_vars, &cnf_predict.num_clauses);

        std::vector<std::pair<int, int>> edges;
        for (int c = 0; c < cnf_predict.num_clauses; ++c)
        {
            int curlit;

            ifs >> curlit;
            while (curlit != 0)
            {
                edges.push_back(std::make_pair(c, curlit < 0 ? (-curlit) - 1 + cnf_predict.num_vars : curlit - 1));
                ifs >> curlit;
            }
        }
        cnf_predict.num_edges = (int)edges.size();
        cnf_predict.edges = new int[edges.size()][2];
        for (int i = 0; i < (int)edges.size(); ++i)
        {
            cnf_predict.edges[i][0] = edges[i].first;
            cnf_predict.edges[i][1] = edges[i].second;
        }
        cnf_predict.output = new int[cnf_predict.num_vars];

        Py_InitializeEx(0);
        _import_array();

        PyObject *module_sys = NULL, *pathlist = NULL, *pathstr = NULL;
        char cwd[1024];
        if (getcwd(cwd, 1024) == NULL)
        {
            fprintf(stderr, "getcwd() failed.");
            exit(-1);
        }
        pathstr = PyUnicode_FromString(cwd);
        module_sys = PyImport_ImportModule("sys");
        pathlist = PyObject_GetAttrString(module_sys, "path");
        PyList_Append(pathlist, pathstr);

        {
            sat_predict::SATPredict predict{gpu_list.c_str(), load_model.c_str()};
            predict.predict(cnf_predict.num_vars, cnf_predict.num_clauses, cnf_predict.num_edges, cnf_predict.edges, cnf_predict.output);
        }
        Py_Finalize();
    }
    else
    {
        std::ifstream ifs{predictfile.c_str()};
        // double predict_time = 0;
        ifs>>cnf_predict.num_vars>>cnf_predict.num_clauses;
        ifs>>predict_time;
        cnf_predict.output = new int[cnf_predict.num_vars];
        for(int i = 0; i < cnf_predict.num_vars; ++i)
            ifs>>cnf_predict.output[i];
    }

    fprintf(stdout, "p ");
    for (int i = 0; i < (int)cnf_predict.num_vars; ++i)
        fprintf(stdout, "%d ", cnf_predict.output[i]);
    fprintf(stdout, "\n");
    return true;
}

#endif
