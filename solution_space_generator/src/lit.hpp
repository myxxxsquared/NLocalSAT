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

#ifndef SAT_LIT_HEADER
#define SAT_LIT_HEADER

namespace sat
{
class Lit
{
    int _value;

  public:
    inline explicit Lit(int val) : _value(val) {}
    inline Lit(int index, bool sign) : _value((index << 1) | sign) {}
    inline Lit operator~() const { return Lit(this->_value ^ 1); }
    inline int index() const { return this->_value >> 1; }
    inline bool sign() const { return (bool)(this->_value & 1); }
    inline int value() const { return this->_value; }

    inline bool operator<(const Lit &rhs) const { return this->_value < rhs._value; }
    inline bool operator==(const Lit &rhs) const { return this->_value == rhs._value; }
};
}

#endif
