
#include "satassert.hpp"

#include <stdexcept>
#include <cstdio>

namespace sat
{

[[noreturn]] int _sat_assert_fault(const char* expr, const char* file, int line)
{
    char errorbuffer[128];
    snprintf(errorbuffer, 128, "Assertion failed: %s:%d (%s)\n", file, line, expr);
    fprintf(stderr, "%s", errorbuffer);
#ifdef SAT_DEBUG
    *(intptr_t*)(0) = 0;
#endif
    throw std::runtime_error(errorbuffer);
}

}
