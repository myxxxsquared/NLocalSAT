/****************************************************************************[CoprocessorThreads.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef COPROCESSORTHREADS_HH
#define COPROCESSORTHREADS_HH

#include "coprocessor-src/CoprocessorTypes.h"

#include "utils/LockCollection.h"

#include <vector>
#include <iostream>

using namespace Minisat;
using namespace std;

namespace Coprocessor {

/** Data Structures that are required to control parallel simplification
 */

/** Object that represents a single job that could be executed by a thread
 */
class Job{
public:

	void* (*function)(void *argument);
	void* argument;
	
	/** constructor, gives the job a unique (32bit) id
	 */
	Job(){
		function = 0;
		argument = 0;
	};
	
	Job( void* (*f)(void *), void* a)
	: function( f ), argument(a)
	{};
};

/** represent the states that a thread can have */
enum ThreadState {
  initializing,  // thread is still setting up, creating the environment
  waiting,       // thread waits for the master to receive a new task
  working,       // thread is currently handling the last job it has been assigned
  finished,      // thread finished its current job and is now waiting for the master to acknowledge
  aborting,      // thread will abort its execution and finish its execution
};

/** main class for thread data, store the data a thread can have */
class ThreadData {
  Job job;               // current / last job of the thread
  ThreadState state;     // current state of the thread
  SleepLock ownLock;     // lock to synchronize with the mast in a sleep state
  SleepLock* masterLock; // pointer to masters lock for synchronization
  
#ifndef __APPLE__ // Does not work on OS-X
  char dummy [128 - sizeof(Job) - sizeof(ThreadState) - sizeof(SleepLock) - sizeof(SleepLock*) ]; // at least on cacheline as dummy!
#else
  char dummy [256 - sizeof(Job) - sizeof(ThreadState) - sizeof(SleepLock) - sizeof(SleepLock*) ]; // at least on cacheline as dummy!
#endif
  
public:
  ThreadData(SleepLock* _masterLock) : state(initializing), masterLock(_masterLock) {}
  
  /** main thread method */
  void run();
  
  /** state getter and setter */
  bool isWorking()      const { return state == working; }
  bool isWaiting()      const { return state == waiting; }
  bool isFinished()     const { return state == finished; }
  bool isInitializing() const { return state == initializing; }
  void setWaiting()           { assert(state == finished && "Thread has to be finished before it can wait" ); state = waiting; }

  /** give a new job to the thread, thread has to be in waiting state */
  void performTask( Job newJob ); 

  /** to awake the thread */
  void awake();
  
  /** to shut down the thread */
  void sendShutdown();
 
  /** method to start thread
   * @param threadData pointer to the threadData object for the current thread
   */
  static void* executeThread(void* threadData);
};

/** main class to controll the execution of multiple threads */
class ThreadController
{
  int32_t threads;          // number of threads that should be used by this object
  SleepLock masterLock;     // lock to be able to wait for threads in a sleep state
  
  pthread_t* threadHandles; // handler to each thread
  ThreadData** data;         // data for each thread
  
public:
  /** set up the threads, wait for them to finish initialization */
  ThreadController(int _threads);
  ~ThreadController(); 
  
  /** initializes the controller object */
  void init();
  
  /** pass jobs to threads, size of vector has to be number of threads! */
  void runJobs( vector<Job>& jobs );
  
  /** pass a single job to the threads */
  bool submitJob( Coprocessor::Job& job );
  
  /** waits until at least one thread is waiting again (can be used to submit jobs in any order */
  void waitForOneFinished();
  
  /** waits until all threads are finished */
  void waitForAllFinished();
  
  /** return the number of threads */
  unsigned size() const { return threads; }
};

/*
 * 
 *  IMPLEMENTATION SECTION FOR LONGER METHODS
 * 
 */


inline void* ThreadData::executeThread(void* threadData)
{
  pthread_attr_t attr;       // create a joinable thread
  pthread_attr_init (&attr);
  pthread_attr_setdetachstate (&attr, PTHREAD_CREATE_JOINABLE);
  
  ThreadData* tData = (ThreadData*) threadData;
  tData->run(); // there is no data to pass to the function
  return 0;
}

inline void ThreadData::performTask(Job newJob)
{
  assert( isWaiting() && "thread has to be waiting before a new job can be assigned" );
  job = newJob;    // assign new job
  state = working; // set state to working
  ownLock.awake(); // awake thread so that it can execute its task
}

inline void ThreadData::awake()
{
  ownLock.awake();
}

inline void ThreadData::sendShutdown()
{
  assert( state == waiting && "Thread should be waiting when it should be aborted" );
  state = aborting;
}


inline void ThreadData::run()
{
   // lock secures execution and state changes
  ownLock.lock();
  assert( state == initializing && "initial state of the thread has to be initializing");
  state = waiting;
  masterLock->awake();
  ownLock.sleep();
  
  // perform parallel work until abort
  while( state != aborting )
  {
    assert(state == working && "state of the worker should be working" );
    // do current work of piece    
    job.function( job.argument );
    // change to finished and go sleeping
    state = finished;
    // notify master
    masterLock->awake();
    // go sleep
    ownLock.sleep();
    // awake
  }
  ownLock.unlock();
}

inline ThreadController::ThreadController(int _threads)
: threads( _threads ), threadHandles(0), data(0)
{}

inline ThreadController::~ThreadController()
{
    // tell everybody that work is over!
    for( int i = 0 ; i < threads; ++i ){
      data[i]->sendShutdown();
      data[i]->awake();
    }
    // join all threads
    for( int i = 0 ; i < threads; ++i ){
        void* status;
        pthread_join( threadHandles[i], &status);
    }
    // delete thread-handles
    if (threadHandles != 0) 
        delete[] threadHandles;

    // delete thread-data
    for( int i = 0; i < threads; ++i)
    {
        delete data[i];
        data[i] = 0;
    }
    if (data != 0) delete[] data;
}

inline void ThreadController::init()
{
  if( threads == 0 ) return;
  cerr << "c init thread controller with " << threads << " threads" << endl;
  threadHandles = new pthread_t [ threads ];
  
  data = new ThreadData* [ threads ];
  
  cerr << "c created pointer to data " << endl;
  
  // create threads for all except the first data object
  for( int i = 0 ; i < threads; ++i ){
    cerr << "c create object " << i << endl;
    data[i] = new ThreadData( &masterLock );
    cerr << "c create object thread " << i << endl;
    pthread_create( & (threadHandles[i]), 0, ThreadData::executeThread , data[i] ); // create thread
  }
    
  cerr << "c wait for initialize " << endl;
  
  int done = 0; // calling thread is thread nr0!
  masterLock.lock();
  while ( done < threads )
  {
    for( ; done < threads; done ++ )
    {
     // thread still does something
     if( data[done]->isInitializing() ) break;
    }
    if( done != threads ) masterLock.sleep();
  }
  masterLock.unlock();
  cerr << "c init done" << endl;
}

inline void ThreadController::runJobs(vector< Job >& jobs)
{
  assert( jobs.size() <= threads && "More jobs than threads cannot be handled at the moment" );
  // submit all jobs
  for( int i = 0 ; i < threads; i++ )
  {
    assert( data[i]->isWaiting() && "Thread has to be waiting when a new job should be assigned" );
    data[i]->performTask(jobs[i]);
  }
  // wait for all threads to finish
  waitForAllFinished ();
}

inline bool ThreadController::submitJob(Job& job)
{
  if( threads == 0 ) return false;
  for( int done = 0; done < threads; done ++ )
  {
    // found a finished thread -> return to user!
    if( data[done]->isWaiting() ) { 
      data[done]->performTask(job);
      return true;
    }
  }
  return false;
}

inline void ThreadController::waitForAllFinished()
{
  if( threads == 0 ) return;
  int done = 0;
  masterLock.lock();
  while ( done < threads )
  {
    for( ; done < threads; done ++ )
    {
      // thread still does something
      if( data[done]->isWorking() ) break;
      // set all done thread to "ready"
      if( data[done]->isFinished() ) { 
        data[done]->setWaiting();
      }
    }
    if( done != threads ) masterLock.sleep();
  }
  masterLock.unlock();
}

inline void ThreadController::waitForOneFinished()
{
  if( threads == 0 ) return;
  masterLock.lock();
  while ( true )
  {
    for( int done = 0; done < threads; done ++ )
    {
      // found a finished thread -> return to user!
      if( data[done]->isFinished() || data[done]->isWaiting() ) { 
        data[done]->setWaiting();
        return;
      }
    }
    masterLock.sleep();
  }
  masterLock.unlock();
}



}

#endif
