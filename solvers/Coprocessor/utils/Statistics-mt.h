/** Norbert Manthey, 02.07.2012
 *  multi-thread safe statistics
 */

#ifndef STATISTICS_H
#define STATISTICS_H

#include "utils/LockCollection.h"

#include <vector>
#include <string>
#include <sstream>
#include <assert.h>
#include <iostream>

using namespace std;

/** class that can take care of statistic tracking in a multi-thread environment
 */
class Statistics {

  vector < int > integerData;
  vector <string> intNames;
  
  vector < double > doubleData;
  vector <string> doubleNames;
  
  //Lock lockI; // lock for integer operations
  //Lock lockD; // lock for double operations
  
public:
  
  Statistics () 
//   : 
//   lockI(),
//   lockD()
  {};
  
  /** return the number of registered entries
   */
  unsigned size() { return intNames.size() + doubleNames.size(); }
  
  /** return the key of a given index
   */
  string& getName( unsigned index ){ return  (index < intNames.size()) ? intNames[index] : doubleNames[index - intNames.size() ]; }
  
  /** return whether a given index is an int value
   */
  bool isInt( unsigned index ) { return index < intNames.size(); };
  
  /** return the int data of a given index
   * Note: check with isInt before!
   */
  int giveInt( unsigned index ) { assert( index < intNames.size() ); return integerData[index]; }

  /** return the int data of a given index
   * Note: check with isInt before!
   */
  int giveDouble( unsigned index ) { assert( index >= intNames.size() ); return doubleData[index]; }
  
  /** register statistic value for integer values
   *  @return id of the register for this statistic value
   */
  unsigned registerI( const string& name, const int firstValue = 0 ) {
    unsigned ret = 0;
//    lockI.wait();
    ret = integerData.size();
    integerData.push_back( firstValue );
    intNames.push_back( name );
//    lockI.unlock();
    return ret;
  }
  
  /** return the id of an already registered event, if it exists, otherwise, create it with 0
   * 
   */
  unsigned reregisterI( const string& name ) {

    for( unsigned i = 0 ; i < intNames.size(); ++i )
    {
      // check each name whether it matches the name to register
      if( intNames[i] == name ) {
	return i;
      }
    }  
    unsigned ret;
    // if the entry has not been found, create it!
    ret = integerData.size();
    integerData.push_back( 0 );
    intNames.push_back( name );
    return ret;
  }
  
  /** register statistic value for integer values
   *  @return id of the register for this statistic value
   */
  unsigned registerD( const string& name, const double firstValue = 0 ) {
    unsigned ret = 0;
//    lockD.wait();
    ret = doubleData.size();
    doubleData.push_back( firstValue );
    doubleNames.push_back( name );
//    lockD.unlock();
    return ret;
  }
  
  /** return the id of an already registered event, if it exists, otherwise, create it with 0
   * 
   */
  unsigned reregisterD( const string& name ) {
//    lockD.wait();
    for( unsigned i = 0 ; i < doubleNames.size(); ++i )
    {
      // check each name whether it matches the name to register
      if( doubleNames[i] == name ) {
//	lockD.unlock();
	return i;
      }
    }
//    lockD.unlock();
    // if the entry has not been found, create it!
    return registerD( name );
  }
  
  /** alter an registered integer value
   * @param id id of the register for the statistics value that should be changed
   * @param diff value that should be added to the data (could be negative!)
   */
  int changeI( const unsigned id, const int diff )
  {
    assert( id < integerData.size() && "registered value has to be inside the statistics int object" );
    int ret = 0;
//    lockI.wait();
    integerData[id] += diff;
    ret = integerData[id];
//    lockI.unlock();
    return ret;
  }
  
  /** alter an registered integer value
   * @param id id of the register for the statistics value that should be changed
   * @param diff value that should be added to the data (could be negative!)
   */
  double changeD( const unsigned id, const double diff )
  {
    assert( id < doubleData.size() && "registered value has to be inside the statistics double object" );
    double ret = 0;
//    lockD.wait();
    doubleData[id] += diff;
    ret = doubleData[id];
//    lockD.unlock();
    return ret;
  }
  
  /** get the value of an int object
   */
  int getI( const unsigned id )
  {
    assert( id < integerData.size() && "registered value has to be inside the statistics int object" );
    int ret = 0;
//    lockI.wait();
    ret = integerData[id];
//    lockI.unlock();
    return ret;
  }
  
  /** get the value of an int object
   */
  double getD( const unsigned id )
  {
    assert( id < doubleData.size() && "registered value has to be inside the statistics int object" );
    double ret = 0;
//    lockD.wait();
    ret = doubleData[id];
//    lockD.unlock();
    return ret;
  }
  
  /** prints all data of objects to a string
   */
  void print( string& output )
  {
//    lockI.wait();
    stringstream s;
    assert( integerData.size() == intNames.size() && "number of data elements and names has to be the same" );
    for( int i = 0 ; i < integerData.size(); ++i ) {
      s << "c [STAT] " << intNames[i] << " : " << integerData[i] << endl;
    }
//    lockI.unlock();
    
//    lockD.wait();
    assert( doubleData.size() == doubleNames.size() && "number of data elements and names has to be the same" );
    for( int i = 0 ; i < doubleData.size(); ++i ) {
      s << "c [STAT] " << doubleNames[i] << " : " << doubleData[i] << endl;
    }
//    lockD.unlock();
    output = s.str();
  }
  
};


extern Statistics statistics;

#endif
