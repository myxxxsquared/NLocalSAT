
#include <algorithm>
#include <stdexcept>

#include <boost/python/object.hpp>

class Lit
{
    int _value;

public:
    inline explicit Lit(int val) : _value(val) {}
    inline Lit(int index, bool sign) : _value((index << 1) | sign) {}
    inline Lit operator~() const { return Lit(this->_value ^ 1); }
    inline int index() const { return this->_value >> 1; }
    inline bool sign() const { return (bool)(this->_value & 1); }
    inline int value() const { return this->_value; }

    inline bool operator<(const Lit &rhs) const { return this->_value < rhs._value; }
    inline bool operator==(const Lit &rhs) const { return this->_value == rhs._value; }

    inline static Lit fromvalue(int val) { return Lit(std::abs(val) - 1, val > 0); }
    inline int tovalue() const { return sign() ? index() + 1 : -index() + 1; }
};

#define DEFINE_SAT_EXCEPTIOJN(expname, baseclass)   \
    struct expname : baseclass                      \
    {                                               \
    public:                                         \
        inline expname(const char *message) throw() \
            : baseclass(message){};                 \
    }

DEFINE_SAT_EXCEPTIOJN(sat_bad_file, std::runtime_error);
DEFINE_SAT_EXCEPTIOJN(sat_bad_format, std::runtime_error);
DEFINE_SAT_EXCEPTIOJN(sat_no_solution, std::runtime_error);

class Problem
{
public:
    inline Problem() : sat_problem(), num_vars(0) {}
    std::vector<std::vector<Lit>> sat_problem;
    std::vector<int> sat_solution;
    int num_vars;
    inline int get_num_vars() const { return num_vars; }
    inline int get_num_clauses() const { return (int)sat_problem.size(); }
    void save(const char *filename) const;
    void load(const char *filename);
    void load_solution(const char *filename);

    boost::python::object to_data() const;

    std::vector<Problem> split(int num_vars);
};

class BatchGenerator
{
    std::vector<std::tuple<int, int, int>> edges;
    std::vector<int> labels;

    int num_vars, num_clauses;

public:
    BatchGenerator();
    bool append(const Problem &problem, int verbose = 0);
    inline int n_vars() const { return num_vars; }
    inline int n_clauses() const { return num_clauses; }
    inline int n_lits() const { return edges.size(); }
    boost::python::object save();
};
