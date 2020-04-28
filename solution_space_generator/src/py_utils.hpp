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

#ifndef PY_UTILS_HEADER
#define PY_UTILS_HEADER

#ifndef MYLIBRARY_USE_IMPORT
#define NO_IMPORT
#endif

#define PY_ARRAY_UNIQUE_SYMBOL SAT_LIBRARY_ARRAY_API
#define PY_UFUNC_UNIQUE_SYMBOL SAT_LIBRARY_ARRAY_API
#define NPY_NO_DEPRECATED_API NPY_1_7_API_VERSION

#include <Python.h>
#include <numpy/ndarrayobject.h>

class PyAllowThreads
{
  public:
    inline PyAllowThreads() : _state(PyEval_SaveThread()) {}
    inline ~PyAllowThreads()
    {
        PyEval_RestoreThread(_state);
    }

  private:
    PyThreadState *_state;
};

class PyEnsureGIL
{
  public:
    inline PyEnsureGIL() : _state(PyGILState_Ensure()) {}
    inline ~PyEnsureGIL()
    {
        PyGILState_Release(_state);
    }

  private:
    PyGILState_STATE _state;
};

#endif
