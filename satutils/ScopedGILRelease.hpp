
#include <boost/python.hpp>

class ScopedGILRelease {
public:
    ScopedGILRelease(const ScopedGILRelease&) = delete;
    ScopedGILRelease& operator=(const ScopedGILRelease&) = delete;

    inline ScopedGILRelease() { m_thread_state = PyEval_SaveThread(); }
    inline ~ScopedGILRelease() {
        PyEval_RestoreThread(m_thread_state);
        m_thread_state = NULL;
    }
private:
    PyThreadState* m_thread_state;
};
