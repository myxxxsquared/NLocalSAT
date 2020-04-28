/***************************************************************************************[Options.h]
Copyright (c) 2008-2010, Niklas Sorensson

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

#ifndef Minisat_Options_h
#define Minisat_Options_h

#include <stdlib.h>
#include <stdio.h>
#include <math.h>
#include <cstring>
#include <string>
#include <sstream>

#include "mtl/IntTypes.h"
#include "mtl/Vec.h"
#include "utils/ParseUtils.h"
#include "mtl/Sort.h"

namespace Minisat {

//==================================================================================================
// Top-level option parse/help functions:


extern void parseOptions     (int& argc, char** argv, bool strict = false);
extern void printUsageAndExit(int  argc, char** argv, bool verbose = false);
extern void setUsageHelp     (const char* str);
extern void setHelpPrefixStr (const char* str);

extern void configCall(int argc, char** argv, std::stringstream& s);

//==================================================================================================
// Options is an abstract class that gives the interface for all types options:


class Option
{
 public:
    const char* name;
    const char* description;
    const char* category;
    const char* type_name;

 
    static vec<Option*>& getOptionList () { static vec<Option*> options; return options; }
    static const char*&  getUsageString() { static const char* usage_str; return usage_str; }
    static const char*&  getHelpPrefixString() { static const char* help_prefix_str = ""; return help_prefix_str; }

 
    struct OptionLt {
        bool operator()(const Option* x, const Option* y) {
            int test1 = strcmp(x->category, y->category);
            return test1 < 0 || test1 == 0 && strcmp(x->type_name, y->type_name) < 0;
        }
    };

    Option(const char* name_, 
           const char* desc_,
           const char* cate_,
           const char* type_,
	   vec<Option*>* externOptionList ) : // push to this list, if present!
      name       (name_)
    , description(desc_)
    , category   (cate_)
    , type_name  (type_)
    { 
      if( externOptionList == 0 ) getOptionList().push(this); 
      else externOptionList->push( this );
    }

 public:
    virtual ~Option() {}

    virtual bool parse             (const char* str)      = 0;
    virtual void help              (bool verbose = false) = 0;
    virtual void giveRndValue      (std::string& optionText ) = 0; // return a valid option-specification as it could appear on the command line
    
    virtual bool hasDefaultValue   () = 0; 				// check whether the current value corresponds to the default value of the option
    virtual void printOptionCall   (std::stringstream& strean ) = 0; 	// print the call that is required to obtain that this option is set

    friend  void parseOptions      (int& argc, char** argv, bool strict);
    friend  void printUsageAndExit (int  argc, char** argv, bool verbose);
    friend  void setUsageHelp      (const char* str);
    friend  void setHelpPrefixStr  (const char* str);
};


//==================================================================================================
// Range classes with specialization for floating types:


struct IntRange {
    int begin;
    int end;
    IntRange(int b, int e) : begin(b), end(e) {}
};

struct Int64Range {
    int64_t begin;
    int64_t end;
    Int64Range(int64_t b, int64_t e) : begin(b), end(e) {}
};

struct DoubleRange {
    double begin;
    double end;
    bool  begin_inclusive;
    bool  end_inclusive;
    DoubleRange(double b, bool binc, double e, bool einc) : begin(b), end(e), begin_inclusive(binc), end_inclusive(einc) {}
};


//==================================================================================================
// Double options:


class DoubleOption : public Option
{
 protected:
    DoubleRange range;
    double      value;
    double      defaultValue; // the value that is given to this option during construction

 public:
    DoubleOption(const char* c, const char* n, const char* d, double def = double(), DoubleRange r = DoubleRange(-HUGE_VAL, false, HUGE_VAL, false), vec<Option*>* externOptionList = 0)
        : Option(n, d, c, "<double>", externOptionList), range(r), value(def), defaultValue(def) {
        // FIXME: set LC_NUMERIC to "C" to make sure that strtof/strtod parses decimal point correctly.
    }

    operator      double   (void) const { return value; }
    operator      double&  (void)       { return value; }
    DoubleOption& operator=(double x)   { value = x; return *this; }

    virtual bool hasDefaultValue ( ) { return value == defaultValue; }
    virtual void printOptionCall (std::stringstream& s ) {
      s << "-" << name << "=" << value;
    }
    
    virtual bool parse(const char* str){
        const char* span = str; 

        if (!match(span, "-") || !match(span, name) || !match(span, "="))
            return false;

        char*  end;
        double tmp = strtod(span, &end);

        if (end == NULL) 
            return false;
        else if (tmp >= range.end && (!range.end_inclusive || tmp != range.end)){
            fprintf(stderr, "ERROR! value <%s> is too large for option \"%s\".\n", span, name);
            exit(2);
        }else if (tmp <= range.begin && (!range.begin_inclusive || tmp != range.begin)){
            fprintf(stderr, "ERROR! value <%s> is too small for option \"%s\".\n", span, name);
            exit(2); }

        value = tmp;
        // fprintf(stderr, "READ VALUE: %g\n", value);

        return true;
    }

    virtual void help (bool verbose = false){
        fprintf(stderr, "  -%-12s = %-8s %c%4.2g .. %4.2g%c (default: %g)\n", 
                name, type_name, 
                range.begin_inclusive ? '[' : '(', 
                range.begin,
                range.end,
                range.end_inclusive ? ']' : ')', 
                value);
#ifndef NOVERBHELP
        if (verbose){
            fprintf(stderr, "\n        %s\n", description);
            fprintf(stderr, "\n");
        }
#endif
    }
    
    void giveRndValue (std::string& optionText ) {
      double rndV = range.begin_inclusive ? range.begin : range.begin + 0.000001;
      rndV += rand();
      while( rndV > range.end ) rndV -= range.end - range.begin;
      std::ostringstream strs;
      strs << rndV;
      optionText = "-" + optionText + "=" + strs.str();
    }
};


//==================================================================================================
// Int options:


class IntOption : public Option
{
 protected:
    IntRange range;
    int32_t  value;
    int32_t  defaultValue;

 public:
    IntOption(const char* c, const char* n, const char* d, int32_t def = int32_t(), IntRange r = IntRange(INT32_MIN, INT32_MAX), vec<Option*>* externOptionList = 0)
        : Option(n, d, c, "<int32>", externOptionList), range(r), value(def), defaultValue(def) {}
 
    operator   int32_t   (void) const { return value; }
    operator   int32_t&  (void)       { return value; }
    IntOption& operator= (int32_t x)  { value = x; return *this; }

    virtual bool hasDefaultValue ( ) { return value == defaultValue; }
    virtual void printOptionCall (std::stringstream& s ) {
      s << "-" << name << "=" << value;
    }
    
    virtual bool parse(const char* str){
        const char* span = str; 

        if (!match(span, "-") || !match(span, name) || !match(span, "="))
            return false;

        char*   end;
        int32_t tmp = strtol(span, &end, 10);

        if (end == NULL) 
            return false;
        else if (tmp > range.end){
            fprintf(stderr, "ERROR! value <%s> is too large for option \"%s\".\n", span, name);
            exit(2);
        }else if (tmp < range.begin){
            fprintf(stderr, "ERROR! value <%s> is too small for option \"%s\".\n", span, name);
            exit(2); }

        value = tmp;

        return true;
    }

    virtual void help (bool verbose = false){
        fprintf(stderr, "  -%-12s = %-8s [", name, type_name);
        if (range.begin == INT32_MIN)
            fprintf(stderr, "imin");
        else
            fprintf(stderr, "%4d", range.begin);

        fprintf(stderr, " .. ");
        if (range.end == INT32_MAX)
            fprintf(stderr, "imax");
        else
            fprintf(stderr, "%4d", range.end);

        fprintf(stderr, "] (default: %d)\n", value);
#ifndef NOVERBHELP
        if (verbose){
            fprintf(stderr, "\n        %s\n", description);
            fprintf(stderr, "\n");
        }
#endif
    }
    
    
    void giveRndValue (std::string& optionText ) {
      int rndV = range.begin;
      rndV += rand();
      while( rndV > range.end ) rndV -= range.end - range.begin;
      std::ostringstream strs;
      strs << rndV;
      optionText = "-" + optionText + "=" + strs.str();
    }
};


// Leave this out for visual C++ until Microsoft implements C99 and gets support for strtoll.
#ifndef _MSC_VER

class Int64Option : public Option
{
 protected:
    Int64Range range;
    int64_t  value;
    int64_t  defaultValue;

 public:
    Int64Option(const char* c, const char* n, const char* d, int64_t def = int64_t(), Int64Range r = Int64Range(INT64_MIN, INT64_MAX), vec<Option*>* externOptionList = 0)
        : Option(n, d, c, "<int64>", externOptionList), range(r), value(def), defaultValue(def) {}
 
    operator     int64_t   (void) const { return value; }
    operator     int64_t&  (void)       { return value; }
    Int64Option& operator= (int64_t x)  { value = x; return *this; }

    virtual bool hasDefaultValue ( ) { return value == defaultValue; }
    virtual void printOptionCall (std::stringstream& s ) {
      s << "-" << name << "=" << value;
    }
    
    virtual bool parse(const char* str){
        const char* span = str; 

        if (!match(span, "-") || !match(span, name) || !match(span, "="))
            return false;

        char*   end;
        int64_t tmp = strtoll(span, &end, 10);

        if (end == NULL) 
            return false;
        else if (tmp > range.end){
            fprintf(stderr, "ERROR! value <%s> is too large for option \"%s\".\n", span, name);
            exit(2);
        }else if (tmp < range.begin){
            fprintf(stderr, "ERROR! value <%s> is too small for option \"%s\".\n", span, name);
            exit(2); }

        value = tmp;

        return true;
    }

    virtual void help (bool verbose = false){
        fprintf(stderr, "  -%-12s = %-8s [", name, type_name);
        if (range.begin == INT64_MIN)
            fprintf(stderr, "imin");
        else
            fprintf(stderr, "%4ld", range.begin);

        fprintf(stderr, " .. ");
        if (range.end == INT64_MAX)
            fprintf(stderr, "imax");
        else
            fprintf(stderr, "%4ld", range.end);

        fprintf(stderr, "] (default: %ld)\n", value);
#ifndef NOVERBHELP
        if (verbose){
            fprintf(stderr, "\n        %s\n", description);
            fprintf(stderr, "\n");
        }
#endif
    }
    
    
    void giveRndValue (std::string& optionText ) {
      int64_t rndV = range.begin;
      rndV += rand();
      while( rndV > range.end ) rndV -= range.end - range.begin;
      std::ostringstream strs;
      strs << rndV;
      optionText = "-" + optionText + "=" + strs.str();
    }
};
#endif

//==================================================================================================
// String option:


class StringOption : public Option
{
    const char* value;
    const char* defaultValue;
 public:
    StringOption(const char* c, const char* n, const char* d, const char* def = NULL, vec<Option*>* externOptionList = 0) 
        : Option(n, d, c, "<string>", externOptionList), value(def), defaultValue(def) {}

    operator      const char*  (void) const     { return value; }
    operator      const char*& (void)           { return value; }
    StringOption& operator=    (const char* x)  { value = x; return *this; }

    virtual bool hasDefaultValue ( ) { return value == defaultValue; }
    virtual void printOptionCall (std::stringstream& s ) {
      if( value != 0 ) s << "-" << name << "=" << value;
      else  s << "-" << name << "=\"\"";
    }
    
    virtual bool parse(const char* str){
        const char* span = str; 

        if (!match(span, "-") || !match(span, name) || !match(span, "="))
            return false;

        value = span;
        return true;
    }

    virtual void help (bool verbose = false){
        fprintf(stderr, "  -%-10s = %8s\n", name, type_name);
#ifndef NOVERBHELP
        if (verbose){
            fprintf(stderr, "\n        %s\n", description);
            fprintf(stderr, "\n");
        }
#endif
    }    
    
    
    void giveRndValue (std::string& optionText ) {
      optionText = ""; // NOTE: this could be files or any other thing, so do not consider this (for now - for special strings, another way might be found...)
    }
};


//==================================================================================================
// Bool option:


class BoolOption : public Option
{
    bool value;
    bool defaultValue;

 public:
    BoolOption(const char* c, const char* n, const char* d, bool v, vec<Option*>* externOptionList = 0) 
        : Option(n, d, c, "<bool>", externOptionList), value(v), defaultValue(v) {}

    operator    bool     (void) const { return value; }
    operator    bool&    (void)       { return value; }
    BoolOption& operator=(bool b)     { value = b; return *this; }

    virtual bool hasDefaultValue ( ) { return value == defaultValue; }
    virtual void printOptionCall (std::stringstream& s ) {
      if( value ) s << "-" << name ;
      else s << "-no-" << name ;
    }
    
    virtual bool parse(const char* str){
        const char* span = str; 
        
        if (match(span, "-")){
            bool b = !match(span, "no-");

            if (strcmp(span, name) == 0){
                value = b;
                return true; }
        }

        return false;
    }

    virtual void help (bool verbose = false){

        fprintf(stderr, "  -%s, -no-%s", name, name);

        for (uint32_t i = 0; i < 32 - strlen(name)*2; i++)
            fprintf(stderr, " ");

        fprintf(stderr, " ");
        fprintf(stderr, "(default: %s)\n", value ? "on" : "off");
#ifndef NOVERBHELP
        if (verbose){
            fprintf(stderr, "\n        %s\n", description);
            fprintf(stderr, "\n");
        }
#endif
    }
    
    
    void giveRndValue (std::string& optionText ) {
      int r = rand();
      if( r % 5 > 1 ) { // more likely to be enabled
	optionText = "-" + std::string(name);
      } else {
	optionText = "-no-" + std::string(name);
      }
      
    }
    
};

//=================================================================================================
}

#endif
