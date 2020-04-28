
#include "satassert.hpp"
#include "assign.hpp"

namespace sat
{

Assign::Assign(int len)
{
    sat_assert(len > 0);
    value.reserve(len);
    for (int i = 0; i < len; ++i)
        value.push_back(false);
}

bool Assign::next()
{
    for (int i = 0; i < (int)value.size(); ++i)
    {
        value[i] = !value[i];
        if (value[i])
            return true;
    }
    return false;
}
}
