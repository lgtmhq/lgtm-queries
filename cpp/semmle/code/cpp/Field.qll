// Copyright 2017 Semmle Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under
// the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied. See the License for the specific language governing
// permissions and limitations under the License.

import semmle.code.cpp.Variable
import semmle.code.cpp.Enum
import semmle.code.cpp.exprs.Access

/**
 * A C structure member or C++ non-static member variable.
 */
class Field extends MemberVariable {

  Field() {
    fieldoffsets(this,_,_)
  }

  /**
   * Gets the offset of this field in bytes from the start of its declaring
   * type (on the machine where facts were extracted).
   */
  int getByteOffset() { fieldoffsets(this,result,_) }
}

/**
 * A C structure member or C++ member variable declared with an explicit size in bits.
 *
 * Syntactically, this looks like `int x : 3` in `struct S { int x : 3; };`.
 */
class BitField extends Field {
  BitField() { bitfield(this,_,_) }

  /**
   * Gets the size of this bitfield in bits (on the machine where facts
   * were extracted).
   */
  int getNumBits() { bitfield(this,result,_) }

  /**
   * Gets the value which appeared after the colon in the bitfield
   * declaration.
   *
   * In most cases, this will give the same value as `getNumBits`. It will
   * only differ when the value after the colon is larger than the size of
   * the variable's type. For example, given `int32_t x : 1234`,
   * `getNumBits` will give 32, whereas `getDeclaredNumBits` will give
   * 1234.
   */
  int getDeclaredNumBits() { bitfield(this,_,result) }

  /**
   * Gets the offset of this bitfield in bits from the byte identified by
   * getByteOffset (on the machine where facts were extracted).
   */
  int getBitOffset() { fieldoffsets(this,_,result) }

  predicate isAnonymous() {
    hasName("(unnamed bitfield)")
  }
}
