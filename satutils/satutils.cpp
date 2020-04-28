
#include <boost/python.hpp>
#include <boost/python/tuple.hpp>
#include <boost/python/suite/indexing/vector_indexing_suite.hpp>

#include <string>
#include <fstream>
#include <map>
#include <tuple>

#include "gen_from_solution.hpp"

boost::python::tuple stat_cnf(std::string filename);
void split_cnf(std::string input_file, std::string output_fileprefix, int eachlen, int randomseed, double minsize, bool multisplit);

#define DEFINE_TRANSLATE(expname)                         \
    PyObject *__type_##expname = NULL;                    \
    void __translate_exp_##expname(const expname &e)      \
    {                                                     \
        boost::python::object expinst(e);                 \
        PyErr_SetObject(__type_##expname, expinst.ptr()); \
    }

#define REGISTER_EXP(expname)                                            \
    do                                                                   \
    {                                                                    \
        class_<expname> __cls_##expname{#expname, init<const char *>()}; \
        __cls_##expname.def("what", &expname::what);                     \
        __type_##expname = __cls_##expname.ptr();                        \
    } while (0)

DEFINE_TRANSLATE(sat_bad_file)
DEFINE_TRANSLATE(sat_bad_format)
DEFINE_TRANSLATE(sat_no_solution)

template <class T>
struct VecToList
{
    static PyObject *convert(const std::vector<T> &vec)
    {
        boost::python::list *l = new boost::python::list();
        for (size_t i = 0; i < vec.size(); i++)
        {
            l->append(vec[i]);
        }

        return l->ptr();
    }
};

void init_boost_numpy();

BOOST_PYTHON_MODULE(satutils)
{
    using namespace boost::python;
    def("stat_cnf", stat_cnf);
    def("split_cnf", split_cnf);
    def("init_boost_numpy", init_boost_numpy);
    class_<Problem>("Problem")
        .def("get_num_vars", &Problem::get_num_vars)
        .def("get_num_clauses", &Problem::get_num_clauses)
        .def("save", &Problem::save)
        .def("load", &Problem::load)
        .def("load_solution", &Problem::load_solution)
        .def("split", &Problem::split)
        .def("to_data", &Problem::to_data);
    class_<BatchGenerator>("BatchGenerator")
        .def("append", &BatchGenerator::append)
        .def("save", &BatchGenerator::save)
        .def("n_vars", &BatchGenerator::n_vars)
        .def("n_clauses", &BatchGenerator::n_clauses)
        .def("n_lits", &BatchGenerator::n_lits);

    to_python_converter<std::vector<Problem>, VecToList<Problem>>();

    REGISTER_EXP(sat_bad_file);
    REGISTER_EXP(sat_bad_format);
    REGISTER_EXP(sat_no_solution);
}
