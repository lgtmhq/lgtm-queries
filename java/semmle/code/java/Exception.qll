// Copyright 2018 Semmle Ltd.
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

/**
 * Provides classes and predicates for working with Java exceptions.
 */

import Element
import Type

/**
 * An Exception represents an element listed in the `throws` clause
 * of a method of constructor.
 *
 * For example, `E` is an exception thrown by method `m` in
 * `void m() throws E;`, whereas `T` is an exception _type_ in
 * `class T extends Exception { }`.
 */
class Exception extends Element, @exception {
  /** The type of this exception. */
  RefType getType() { exceptions(this,result,_) }

  /** The callable whose `throws` clause contains this exception. */
  Callable getCallable() { exceptions(this,_,result) }

  /** The name of this exception is the name of its type. */
  string getName() { result = this.getType().getName() }

  /** Holds if this exception has the specified `name`. */
  predicate hasName(string name) { this.getType().hasName(name) }

  string toString() { result = this.getType().toString() }
}
