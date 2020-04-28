
#ifndef PREDICT_HEADER
#define PREDICT_HEADER

typedef struct _object PyObject;

namespace sat_predict
{
class SATPredict
{
    PyObject *satpredict;

public:
    SATPredict(const char* gpu, const char* load_model);

    ~SATPredict();
    void predict(int num_vars, int num_clauses, int num_edges, const int edges[][2], int output[]);
};
} // namespace sat_predict

#endif /* PREDICT_HEADER */
