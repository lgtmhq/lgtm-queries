// Copyright 2016 Semmle Ltd.
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
 * QL predicates for representing various kinds of abstract values.
 *
 * This is internal API and subject to change; use the interface exposed
 * by `semmle.javascript.flow.AbstractValues` and `com.semmle.javascript.flow.InferredTypes`
 * instead.
 */

import AbstractValues
import InferredTypes

// the concrete encoding of our definite abstract values as integers
int theAbstractNullValue()        { result =  0 }  // represents `null`
int theAbstractUndefinedValue()   { result =  1 }  // represents `undefined`
int theAbstractFalseValue()       { result =  2 }  // represents `false`
int theAbstractTrueValue()        { result =  3 }  // represents `true`
int theAbstractZeroValue()        { result =  4 }  // represents `0`
int theAbstractNonZeroValue()     { result =  5 }  // represents non-zero numbers
int theAbstractEmptyValue()       { result =  6 }  // represents `""`
int theAbstractNumStringValue()   { result =  7 }  // represents strings that coerce to a number
int theAbstractOtherStringValue() { result =  8 }  // represents all other strings
int theAbstractFunctionValue()    { result =  9 }  // represents functions
int theAbstractClassValue()       { result = 10 }  // represents classes
int theAbstractDateValue()        { result = 11 }  // represents Date objects
int theAbstractObjectValue()      { result = 12 }  // represents non-Date objects

// types and Boolean coercions of definite abstract values
predicate definiteAbstractValues(int id, InferredType type, boolean toBool) {
  id = theAbstractNullValue()        and type = "null"      and toBool = false or
  id = theAbstractUndefinedValue()   and type = "undefined" and toBool = false or
  id = theAbstractFalseValue()       and type = "boolean"   and toBool = false or
  id = theAbstractTrueValue()        and type = "boolean"   and toBool = true  or
  id = theAbstractZeroValue()        and type = "number"    and toBool = false or
  id = theAbstractNonZeroValue()     and type = "number"    and toBool = true  or
  id = theAbstractEmptyValue()       and type = "string"    and toBool = false or
  id = theAbstractNumStringValue()   and type = "string"    and toBool = true  or
  id = theAbstractOtherStringValue() and type = "string"    and toBool = true  or
  id = theAbstractFunctionValue()    and type = "function"  and toBool = true  or
  id = theAbstractClassValue()       and type = "class"     and toBool = true  or
  id = theAbstractDateValue()        and type = "date"      and toBool = true  or
  id = theAbstractObjectValue()      and type = "object"    and toBool = true
}

// the concrete encoding of our indefinite abstract values as integers
int indefiniteAbstractValue(DataFlowIncompleteness cause) {
  result = -1 and cause = "call" or
  result = -2 and cause = "heap" or
  result = -3 and cause = "import" or
  result = -4 and cause = "global" or
  result = -5 and cause = "yield"
}

/**
 * Relate abstract values to their type and Boolean coercion.
 */
predicate abstractValues(int id, InferredType type, boolean toBool) {
  definiteAbstractValues(id, type, toBool) or
  id = indefiniteAbstractValue(_) and (toBool = true or toBool = false)
}

/**
 * Domain predicate for the `AbstractValue` class that encompasses all
 * encodings of abstract values.
 */
cached predicate abstractValueId(int id) { abstractValues(id, _, _) }

/**
 * Get a definite abstract value with the given type.
 */
int abstractValueOfType(string type) {
  definiteAbstractValues(result, type, _)
}
