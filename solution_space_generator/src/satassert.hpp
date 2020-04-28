
#ifndef SAT_ASSERT_HEADER
#define SAT_ASSERT_HEADER

namespace sat
{
[[noreturn]] int _sat_assert_fault(const char* expr, const char* file, int line);
}

#define sat_assert(expr) (void)((expr) ? 0 : sat::_sat_assert_fault(#expr, __FILE__, __LINE__))

#ifdef SAT_DEBUG
#define sat_assert_debug(expr) sat_assert(expr)
#else
#define sat_assert_debug(expr) (void)(expr)
#endif

#endif
