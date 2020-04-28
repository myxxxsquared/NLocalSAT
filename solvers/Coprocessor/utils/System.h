/****************************************************************************************[System.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_System_h
#define Minisat_System_h

#if defined(__linux__)
#include <fpu_control.h>
#endif

#include "mtl/IntTypes.h"

//-------------------------------------------------------------------------------------------------

namespace Minisat {

static inline double cpuTime(void); // CPU-time in seconds.
static inline double wallClockTime(void); //Wall-Clock-time in seconds
extern double memUsed();            // Memory in mega bytes (returns 0 for unsupported architectures).
extern double memUsedPeak();        // Peak-memory in mega bytes (returns 0 for unsupported architectures).

}

//-------------------------------------------------------------------------------------------------
// Implementation of inline functions:

#if defined(_MSC_VER) || defined(__MINGW32__)
#include <time.h>

static inline double Minisat::cpuTime(void) { return (double)clock() / CLOCKS_PER_SEC; }
#warning WALLCLOCKTIME NOT SUPPORTED HERE
static inline double Minisat::wallClockTime(void) { return (double) clock() / CLOCKS_PER_SEC; }
#else
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#include <time.h>

#ifdef __APPLE__
#include <mach/clock.h>
#include <mach/mach.h>
#endif

static inline double Minisat::cpuTime(void) {
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }


#ifndef __APPLE__ // Mac OS does not support the linux wall clock
static inline double Minisat::wallClockTime(void)
{
    struct timespec timestamp;
    clock_gettime(CLOCK_MONOTONIC, &timestamp);
    return ((double) timestamp.tv_sec) + ((double) timestamp.tv_nsec / 1000000000);
}
#else // use the Mac wall clock instead 
static inline double Minisat::wallClockTime(void)
{
    clock_serv_t cclock;
    mach_timespec_t mts;
    host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &cclock);
    clock_get_time(cclock, &mts);
    mach_port_deallocate(mach_task_self(), cclock);
    return ((double) mts.tv_sec) + ((double) mts.tv_nsec / 1000000000);
}
#endif

#endif

// implement clocks independent on the operating system

/** simple class that combines cpu and wall clock time */
class Clock {
  double cTime,wTime;
public:
  Clock() : cTime(0), wTime(0) {}
  void start() { cTime = Minisat::cpuTime() - cTime; wTime = Minisat::wallClockTime() - wTime; }
  void stop() {  cTime = Minisat::cpuTime() - cTime; wTime = Minisat::wallClockTime() - wTime;  }
  double getCpuTime() const { return cTime; }
  double getWallClockTime() const { return wTime; }
  void reset() { cTime = 0; wTime = 0; }
};

/** Method clock - class that stopes the time from the call until the focus is lost */
class MethodClock {
private:
    Clock& clock;
    bool stopped;
public:
    MethodClock( Clock&c ) : clock(c), stopped(false) { clock.start(); };
    ~MethodClock() { if(!stopped) clock.stop(); }
    void stop() { clock.stop(); stopped = true;}
    void cont() { if( stopped ) {clock.start(); stopped = false;} }
};

#endif
