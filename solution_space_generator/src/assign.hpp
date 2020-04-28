
#ifndef SAT_ASSIGN_HEADER
#define SAT_ASSIGN_HEADER

#include <vector>

namespace sat
{
class Assign
{
  public:
    std::vector<bool> value;
    Assign(int len);
    bool next();
};
}

#endif
