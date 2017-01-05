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

/**
 * QL predicates for representing various kinds of abstract values.
 *
 * This is internal API and subject to change; use the interface exposed
 * by `semmle.javascript.flow.AbstractValues` and `com.semmle.javascript.flow.InferredTypes`
 * instead.
 */

import AbstractValues
private import InferredTypes

newtype TAbstractValue =
  /** Abstract representation of `null`. */
  TAbstractNull() or
  /** Abstract representation of `undefined`. */
  TAbstractUndefined() or
  /** Abstract representation of Boolean values `true` and `false`. */
  TAbstractBoolean(boolean b) { b = true or b = false } or
  /** Abstract representation of the number zero. */
  TAbstractZero() or
  /** Abstract representation of non-zero numbers. */
  TAbstractNonZero() or
  /** Abstract representation of the empty string. */
  TAbstractEmpty() or
  /** Abstract representation of strings that coerce to a number. */
  TAbstractNumString() or
  /** Abstract representation of non-empty strings that do not coerce to a number. */
  TAbstractOtherString() or
  /** Abstract representation of function objects. */
  TAbstractFunction(Function f) or
  /** Abstract representation of class objects. */
  TAbstractClass(Class c) or
  /** Abstract representation of Date objects. */
  TAbstractDate() or
  /** Abstract representation of arguments objects. */
  TAbstractArguments() or
  /** Abstract representation of objects other than functions, classes, dates or arguments. */
  TAbstractObject() or
  /** Abstract representation of indefinite values that represent a function or class. */
  TIndefiniteFunctionOrClass(DataFlowIncompleteness cause) or
  /*** Abstract representation of indefinite values that represent any value. */
  TIndefiniteAbstractValue(DataFlowIncompleteness cause)

library class AbstractNull extends PrimitiveAbstractValue, TAbstractNull {
  boolean getBooleanValue() { result = false }
  PrimitiveType getType() { result = TTNull() }
  predicate isCoercibleToNumber() { none() }
  string toString() { result = "null" }
}

library class AbstractUndefined extends PrimitiveAbstractValue, TAbstractUndefined {
  boolean getBooleanValue() { result = false }
  PrimitiveType getType() { result = TTUndefined() }
  predicate isCoercibleToNumber() { none() }
  string toString() { result = "undefined" }
}

library class AbstractBoolean extends PrimitiveAbstractValue, TAbstractBoolean {
  boolean getBooleanValue() { this = TAbstractBoolean(result) }
  PrimitiveType getType() { result = TTBoolean() }
  predicate isCoercibleToNumber() { any() }
  string toString() { result = getBooleanValue().toString() }
}

library class AbstractZero extends PrimitiveAbstractValue, TAbstractZero {
  boolean getBooleanValue() { result = false }
  PrimitiveType getType() { result = TTNumber() }
  predicate isCoercibleToNumber() { any() }
  string toString() { result = "0" }
}

library class AbstractNonZero extends PrimitiveAbstractValue, TAbstractNonZero {
  boolean getBooleanValue() { result = true }
  PrimitiveType getType() { result = TTNumber() }
  predicate isCoercibleToNumber() { any() }
  string toString() { result = "non-zero value" }
}

library class AbstractEmpty extends PrimitiveAbstractValue, TAbstractEmpty {
  boolean getBooleanValue() { result = false }
  PrimitiveType getType() { result = TTString() }
  predicate isCoercibleToNumber() { any() }
  string toString() { result = "\"\"" }
}

library class AbstractNumString extends PrimitiveAbstractValue, TAbstractNumString {
  boolean getBooleanValue() { result = true }
  PrimitiveType getType() { result = TTString() }
  predicate isCoercibleToNumber() { any() }
  string toString() { result = "numeric string" }
}

library class AbstractOtherString extends PrimitiveAbstractValue, TAbstractOtherString {
  boolean getBooleanValue() { result = true }
  PrimitiveType getType() { result = TTString() }
  predicate isCoercibleToNumber() { none() }
  string toString() { result = "non-empty, non-numeric string" }
}

library class AbstractFunction extends DefiniteAbstractValue, TAbstractFunction {
  boolean getBooleanValue() { result = true }
  InferredType getType() { result = TTFunction() }
  predicate isCoercibleToNumber() { none() }
  PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  string toString() { result = "function" }
}

library class AbstractClass extends DefiniteAbstractValue, TAbstractClass {
  boolean getBooleanValue() { result = true }
  InferredType getType() { result = TTClass() }
  predicate isCoercibleToNumber() { none() }
  PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  string toString() { result = "class" }
}

library class AbstractDate extends DefiniteAbstractValue, TAbstractDate {
  boolean getBooleanValue() { result = true }
  InferredType getType() { result = TTDate() }
  predicate isCoercibleToNumber() { any() }
  PrimitiveAbstractValue toPrimitive() { result.getType() = TTNumber() }
  string toString() { result = "date" }
}

library class AbstractArguments extends DefiniteAbstractValue, TAbstractArguments {
  boolean getBooleanValue() { result = true }
  InferredType getType() { result = TTObject() }
  predicate isCoercibleToNumber() { none() }
  PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  string toString() { result = "arguments" }
}

library class AbstractObject extends DefiniteAbstractValue, TAbstractObject {
  boolean getBooleanValue() { result = true }
  InferredType getType() { result = TTObject() }
  predicate isCoercibleToNumber() { none() }
  PrimitiveAbstractValue toPrimitive() { result.getType() = TTString() }
  string toString() { result = "object" }
}

library class IndefiniteFunctionOrClass extends AbstractValue, TIndefiniteFunctionOrClass {
  boolean getBooleanValue() { result = true }
  InferredType getType() { result = TTFunction() or result = TTClass() }
  predicate isCoercibleToNumber() { none() }
  PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  string toString() { result = "indefinite value (function or class)" }
}

library class IndefiniteAbstractValue extends AbstractValue, TIndefiniteAbstractValue {
  boolean getBooleanValue() { result = true or result = false }
  InferredType getType() { any() }
  predicate isCoercibleToNumber() { any() }
  PrimitiveAbstractValue toPrimitive() { any() }
  string toString() { result = "indefinite value" }
}