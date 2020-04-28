/********************************************************************************[LockCollection.h]
Copyright (c) 2012, All rights reserved, Norbert Manthey

**************************************************************************************************/


#ifndef PARALLEL_HH
#define PARALLEL_HH

#include <cstdio>
#include <iostream>
#include <queue>
#include <signal.h>
#include <stack>
#include <unistd.h>
#include <assert.h>

// for parallel stuff
#include <pthread.h>
#include <semaphore.h>

/** usual lock
 */
class Lock
{
  pthread_mutex_t m;
public:
  /// initially, the lock can be grabbed
  Lock()
  {
    pthread_mutex_init(&m, 0);
  }
  
  /// get the lock
  void lock(){
    pthread_mutex_lock (&m); 
  }
  
  /// release the lock
  void unlock(){
    pthread_mutex_unlock (&m); 
  }
  
  // give the method lock access to the mutex that is inside of a lock class
  friend class MethodLock;
  
};

/** Lock that offers more tricks, basd on a semaphore */
class ComplexLock{
private:

	sem_t _lock;	// actual semaphore
	int _max;	// users for the semaphore (threads that are allowed to share the semaphore at the same time)
public:

	/** create an unlocked lock
	*
	* @param max specify number of maximal threads that have entered the semaphore
	*/
	ComplexLock(int max = 1)
	 : _max( max )
	{
		// create semaphore with no space in it
		sem_init(&(_lock), 0, max);
	}
	
	/** release all used resources (nothing to do -> semaphore becomes invalid)
	*/
	~ComplexLock(){
	}
	
	/** tries to lock
	* @return true, if locking was successful
	*/
	bool trylock(){
		int err = sem_trywait( &_lock );
		return err == 0;
	}
	//@param transitive allow multiple locking of the same thread ?
	
	/** releases one lock again
	*
	* should only be called by the thread that is currently owns the lock
	*/
	void unlock(){
		sem_post( &_lock );
		//fprintf( stderr, "\n\nreleased lock %d\n\n" , (int)*(int*)(void*)&_lock );
	}

	/** waits until the lock is given to the calling thread
	*/	
	void wait(){
		//fprintf( stderr, "\n\nwait for lock %d\n\n" , (int)*(int*)(void*)&_lock );
		sem_wait( &_lock );
		//fprintf( stderr, "\n\nblog lock %d\n\n" , (int)*(int*)(void*)&_lock );
	}

	/** return numbers of waiters in the semaphore
	*/
	int getWaiters(){
	  int ret = 0;
	  sem_getvalue(&_lock, &ret);
	  return ret;
	}
};

/** This class can be created the begin of each method and will be automatically destroyed before the method is left
 */
class MethodLock
{
  pthread_mutex_t& m;
public:
  // when the object is created, the lock is grabbed
  MethodLock( pthread_mutex_t& mutex ) : m(mutex)
  {
    pthread_mutex_lock (&m);  
  }
  MethodLock( Lock& lock ) : m(lock.m)
  {
    pthread_mutex_lock (&m);  
  }
  
  // when the object is destroyed, the lock is released
  ~MethodLock()
  {
    pthread_mutex_unlock (&m);
  }
};

/** locking class, also for waiting 
 * class that offers a mutex combibed with a conditional variable and a boolean variable
 */
class SleepLock
{
  // bool sleeps;               /// is set to true, iff last time somebody called sleep() before awake was called
  pthread_mutex_t mutex;     /// mutex for the lock
  pthread_cond_t master_cv;  /// conditional variable for the lock
  
  // do not allow the outside to copy this lock
  explicit SleepLock(const SleepLock& l )
  {};
  SleepLock& operator=(const SleepLock& l)
  {return *this;}
  
public:
  /** setup the lock
   * @param initialSleep first call to sleep will lead to sleep if the parameter is true (if awake is not called inbetween)
   */
  SleepLock() // : sleeps( initialSleep )
  {
    pthread_mutex_init(&mutex,     0);
    pthread_cond_init (&master_cv, 0);
  }
  
  ~SleepLock()
  {
    // sleeps = false;
    pthread_mutex_destroy(&mutex);
    pthread_cond_destroy (&master_cv);
  }
  
  /// get the lock
  void lock(){
    pthread_mutex_lock (&mutex); 
  }
  
  /// release the lock
  void unlock(){
    pthread_mutex_unlock (&mutex); 
  }
    
  
  /** sleep until somebody calls awake()
   *  Note: should only be called between the lock() and unlock() command!
   *        After waking up again, unlock() has to be called again!
   */
  void sleep(){
    pthread_cond_wait (&master_cv,&mutex); // otherwise sleep now!
  }
  
  /** wakeup all sleeping threads!
   *  Note: waits until it can get the lock
   *        wakes up threads afterwards (cannot run, because calling thread still has the lock)
   *        releases the lock
   */
  void awake()
  {
    pthread_mutex_lock (&mutex);
    pthread_cond_broadcast (&master_cv); // initial attempt will fail!
    pthread_mutex_unlock (&mutex); 
  }
};

/** implement a spin lock based on gcc's atomic operations (perform busy wait) */
class SpinLock {

private:
  /// the integer that is used for locking
    volatile unsigned short _lock;
public:
    SpinLock() 
    : _lock(0)
    {}

    void lock()
    {
        // Aquire once locked==false (atomic)
        while ( _lock != 0 || __sync_bool_compare_and_swap(&_lock, 0, 0xffff) == false) {}
    }

    void unlock()
    {
      // could also be done without atomic operation?!  
       __sync_bool_compare_and_swap(&_lock, 0xffff, 0);
      //_lock = 0;
    }
    
    /** return the current value of the lock (for debug purposes)
     *  Note: this call is not thread safe!
     */
    int getValue() const { return _lock; }
};


/** implement a readers-writer lock based on pthreads rw lock */
class ReadersWriterLock {
private:
    pthread_rwlock_t mutex;
    pthread_rwlockattr_t attr;
public: 
    ReadersWriterLock() 
    {
        pthread_rwlockattr_init(&attr);
        pthread_rwlock_init(&mutex, &attr);
    }
    ~ReadersWriterLock()
    {
        int val = pthread_rwlock_destroy(&mutex);
        assert (val == 0);
        pthread_rwlockattr_destroy(&attr);
    }
    void readLock() 
    {
        pthread_rwlock_rdlock(&mutex);
    }
    void readUnlock() 
    {
        pthread_rwlock_unlock(&mutex);
    }

    void writeLock() 
    {
        pthread_rwlock_wrlock(&mutex);
    }
    void writeUnlock() 
    {
        pthread_rwlock_unlock(&mutex);
    }
    pthread_rwlock_t getValue()
    {
        return mutex;
    }

};

#endif
