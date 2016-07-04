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
 * QL classes for working with abstract values.
 *
 * Abstract values are a finite representation of the potentially
 * infinite set of concrete values observed at runtime.
 *
 * Some abstract values directly correspond to concrete values:
 * for example, there is an abstract `null` value that represents
 * the concrete `null` value.
 *
 * Most abstract values, however, represent a set of concrete
 * values: for example, there is an abstract value `nonzero`
 * representing the set of all non-zero numbers.
 *
 * The flow analysis uses abstract values of the latter kind to
 * finitely overapproximate the infinite set of potential program
 * executions. This entails imprecision of two kinds:
 *
 *   - sometimes we deliberately forget information about a
 *     concrete value because we are not interested in it: for
 *     example, the concrete value `42` is mapped to the abstract
 *     value `nonzero`;
 *
 *   - at other times, the analysis does not have enough information
 *     to precisely model the behaviour of certain program elements:
 *     for example, the current flow analysis is intra-procedural,
 *     so it does not model parameter passing or return values, and
 *     hence has to make worst-case assumptions about the possible
 *     values of parameters or function calls.
 *
 * We use two categories of abstract values to represent these
 * different sources of imprecision: _definite_ abstract values
 * are deliberate overapproximations, while _indefinite_ abstract
 * values are overapproximations arising from incompleteness.
 *
 * Both kinds of abstract values keep track of which concrete objects
 * they represent; additionally, indefinite abstract values record
 * the source of imprecision that caused them to arise.
 */

import javascript
private import AbstractValuesImpl

/**
 * An abstract value inferred by the flow analysis, representing
 * a set of concrete values.
 *
 * Currently, abstract values are encoded as integers, but this
 * representation is an implementation detail and may change in
 * future.
 */
class AbstractValue extends int {
  AbstractValue() { abstractValueId(this) }

  /**
   * Get the type of some concrete value represented by this
   * abstract value.
   */
  InferredType getType() {
    abstractValues(this, result, _)
  }

  /**
   * Get the Boolean value some concrete value represented by this
   * abstract value coerces to.
   */
  boolean getBooleanValue() {
    abstractValues(this, _, result)
  }

  /**
   * Get an abstract primitive value this abstract value coerces to.
   *
   * This abstractly models the `ToPrimitive` coercion described in the
   * ECMAScript language specification.
   */
  PrimitiveAbstractValue toPrimitive() {
    exists (InferredType tp | tp = getType() |
      tp instanceof PrimitiveType and result = abstractValueOfType(tp) or
      (tp = "function" or tp = "class") and result = theAbstractOtherStringValue() or
      tp = "date" and result = abstractValueOfType("number") or
      tp = "object" and result = abstractValueOfType("string")
    )
  }

  /**
   * Is this abstract value coercible to a number, that is, does it
   * represent at least one concrete value for which the `ToNumber`
   * conversion does not yield `NaN`?
   */
  predicate isCoercibleToNumber() {
    this = indefiniteAbstractValue(_) or
    this = abstractValueOfType("boolean") or
    this = abstractValueOfType("number") or
    this = theAbstractNumStringValue() or
    this = abstractValueOfType("date")
  }

  /**
   * Is this abstract value an indefinite value arising from the
   * incompleteness `cause`?
   */
  predicate isIndefinite(DataFlowIncompleteness cause) {
    this = indefiniteAbstractValue(cause)
  }
}

/**
 * A definite abstract value that represents only primitive concrete values.
 */
class PrimitiveAbstractValue extends AbstractValue {
  PrimitiveAbstractValue() {
    exists (PrimitiveType prim | this = abstractValueOfType(prim))
  }

  PrimitiveAbstractValue toPrimitive() {
    result = this
  }

  PrimitiveType getType() {
    result = super.getType()
  }
}
