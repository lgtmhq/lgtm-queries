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
 * Provides classes for working with abstract values.
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
private import InferredTypes

/**
 * An abstract value inferred by the flow analysis, representing
 * a set of concrete values.
 */
class AbstractValue extends TAbstractValue {
  /**
   * Gets the type of some concrete value represented by this
   * abstract value.
   */
  abstract InferredType getType();

  /**
   * Gets the Boolean value some concrete value represented by this
   * abstract value coerces to.
   */
  abstract boolean getBooleanValue();

  /**
   * Gets an abstract primitive value this abstract value coerces to.
   *
   * This abstractly models the `ToPrimitive` coercion described in the
   * ECMAScript language specification.
   */
  abstract PrimitiveAbstractValue toPrimitive();

  /**
   * Holds if this abstract value is coercible to a number, that is, it
   * represents at least one concrete value for which the `ToNumber`
   * conversion does not yield `NaN`.
   */
  abstract predicate isCoercibleToNumber();

  /**
   * Holds if this abstract value is an indefinite value arising from the
   * incompleteness `cause`.
   */
  predicate isIndefinite(DataFlowIncompleteness cause) {
    none()
  }

  /** Gets a textual representation of this element. */
  abstract string toString();
}

/**
 * A definite abstract value, that is, an abstract value that is not
 * affected by analysis incompleteness.
 */
abstract class DefiniteAbstractValue extends AbstractValue {
}

/**
 * A definite abstract value that represents only primitive concrete values.
 */
abstract class PrimitiveAbstractValue extends DefiniteAbstractValue {
  override PrimitiveAbstractValue toPrimitive() {
    result = this
  }

  override abstract PrimitiveType getType();
}

/**
 * An abstract value representing `null`.
 */
class AbstractNull extends PrimitiveAbstractValue, TAbstractNull {
  override boolean getBooleanValue() { result = false }
  override PrimitiveType getType() { result = TTNull() }
  override predicate isCoercibleToNumber() { none() }
  override string toString() { result = "null" }
}

/**
 * An abstract value representing `undefined`.
 */
class AbstractUndefined extends PrimitiveAbstractValue, TAbstractUndefined {
  override boolean getBooleanValue() { result = false }
  override PrimitiveType getType() { result = TTUndefined() }
  override predicate isCoercibleToNumber() { none() }
  override string toString() { result = "undefined" }
}

/**
 * An abstract value representing a Boolean value.
 */
class AbstractBoolean extends PrimitiveAbstractValue, TAbstractBoolean {
  override boolean getBooleanValue() { this = TAbstractBoolean(result) }
  override PrimitiveType getType() { result = TTBoolean() }
  override predicate isCoercibleToNumber() { any() }
  override string toString() { result = getBooleanValue().toString() }
}

/**
 * An abstract value representing the number zero.
 */
class AbstractZero extends PrimitiveAbstractValue, TAbstractZero {
  override boolean getBooleanValue() { result = false }
  override PrimitiveType getType() { result = TTNumber() }
  override predicate isCoercibleToNumber() { any() }
  override string toString() { result = "0" }
}

/**
 * An abstract value representing a non-zero number.
 */
class AbstractNonZero extends PrimitiveAbstractValue, TAbstractNonZero {
  override boolean getBooleanValue() { result = true }
  override PrimitiveType getType() { result = TTNumber() }
  override predicate isCoercibleToNumber() { any() }
  override string toString() { result = "non-zero value" }
}

/**
 * An abstract value representing the empty string.
 */
class AbstractEmpty extends PrimitiveAbstractValue, TAbstractEmpty {
  override boolean getBooleanValue() { result = false }
  override PrimitiveType getType() { result = TTString() }
  override predicate isCoercibleToNumber() { any() }
  override string toString() { result = "\"\"" }
}

/**
 * An abstract value representing a numeric string, that is, a string `s`
 * such that `+s` is not `NaN`.
 */
class AbstractNumString extends PrimitiveAbstractValue, TAbstractNumString {
  override boolean getBooleanValue() { result = true }
  override PrimitiveType getType() { result = TTString() }
  override predicate isCoercibleToNumber() { any() }
  override string toString() { result = "numeric string" }
}

/**
 * An abstract value representing a non-empty, non-numeric string.
 */
class AbstractOtherString extends PrimitiveAbstractValue, TAbstractOtherString {
  override boolean getBooleanValue() { result = true }
  override PrimitiveType getType() { result = TTString() }
  override predicate isCoercibleToNumber() { none() }
  override string toString() { result = "non-empty, non-numeric string" }
}

/**
 * An abstract value representing an individual function.
 */
class AbstractFunction extends DefiniteAbstractValue, TAbstractFunction {
  /**
   * Gets the function represented by this abstract value.
   */
  Function getFunction() {
    this = TAbstractFunction(result)
  }

  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTFunction() }
  override predicate isCoercibleToNumber() { none() }
  override PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  override string toString() { result = "function" }
}

/**
 * An abstract value representing an individual class.
 */
class AbstractClass extends DefiniteAbstractValue, TAbstractClass {
  /**
   * Gets the class represented by this abstract value.
   */
  Class getClass() {
    this = TAbstractClass(result)
  }

  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTClass() }
  override predicate isCoercibleToNumber() { none() }
  override PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  override string toString() { result = "class" }
}


/**
 * An abstract value representing a `Date` object.
 */
class AbstractDate extends DefiniteAbstractValue, TAbstractDate {
  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTDate() }
  override predicate isCoercibleToNumber() { any() }
  override PrimitiveAbstractValue toPrimitive() { result.getType() = TTNumber() }
  override string toString() { result = "date" }
}

/**
 * An abstract value representing an `arguments` object.
 */
class AbstractArguments extends DefiniteAbstractValue, TAbstractArguments {
  /** Gets the function whose `arguments` object this is an abstraction of. */
  Function getFunction() {
    this = TAbstractArguments(result)
  }

  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTObject() }
  override predicate isCoercibleToNumber() { none() }
  override PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  override string toString() { result = "arguments" }
}

/**
 * An abstract value representing the global object.
 */
class AbstractGlobalObject extends DefiniteAbstractValue, TAbstractGlobalObject {
  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTObject() }
  override predicate isCoercibleToNumber() { none() }
  override PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  override string toString() { result = "global" }
}

/**
 * An abstract value representing an object not covered by the other abstract
 * values.
 */
class AbstractOtherObject extends DefiniteAbstractValue, TAbstractOtherObject {
  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTObject() }
  override predicate isCoercibleToNumber() { none() }
  override PrimitiveAbstractValue toPrimitive() { result.getType() = TTString() }
  override string toString() { result = "object" }
}

/**
 * An indefinite abstract value representing an unknown function or class.
 */
class IndefiniteFunctionOrClass extends AbstractValue, TIndefiniteFunctionOrClass {
  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTFunction() or result = TTClass() }
  override predicate isCoercibleToNumber() { none() }
  override PrimitiveAbstractValue toPrimitive() { result = TAbstractOtherString() }
  override predicate isIndefinite(DataFlowIncompleteness cause) {
    this = TIndefiniteFunctionOrClass(cause)
  }
  override string toString() {
    exists (DataFlowIncompleteness cause | isIndefinite(cause) |
      result = "indefinite function or class (" + cause + ")"
    )
  }
}

/**
 * An indefinite abstract value representing an unknown object.
 */
class IndefiniteObject extends AbstractValue, TIndefiniteObject {
  override boolean getBooleanValue() { result = true }
  override InferredType getType() { result = TTDate() or result = TTObject() }
  override predicate isCoercibleToNumber() { any() }
  override PrimitiveAbstractValue toPrimitive() {
    result.getType() = TTString() or result.getType() = TTNumber()
  }
  override predicate isIndefinite(DataFlowIncompleteness cause) {
    this = TIndefiniteObject(cause)
  }
  override string toString() {
    exists (DataFlowIncompleteness cause | isIndefinite(cause) |
      result = "indefinite object (" + cause + ")"
    )
  }
}

/**
 * An indefinite abstract value representing an unknown value.
 */
class IndefiniteAbstractValue extends AbstractValue, TIndefiniteAbstractValue {
  override boolean getBooleanValue() { result = true or result = false }
  override InferredType getType() { any() }
  override predicate isCoercibleToNumber() { any() }
  override PrimitiveAbstractValue toPrimitive() { any() }
  override predicate isIndefinite(DataFlowIncompleteness cause) {
    this = TIndefiniteAbstractValue(cause)
  }
  override string toString() {
    exists (DataFlowIncompleteness cause | isIndefinite(cause) |
      result = "indefinite value (" + cause + ")"
    )
  }

  /**
   * Gets an abstract value representing a subset of the concrete values represented by
   * this abstract value.
   *
   * Taken together, all results of this predicate taken together must cover the entire
   * set of concrete values represented by this abstract value.
   */
  AbstractValue split() {
    exists (string cause | isIndefinite(cause) |
      result = TIndefiniteFunctionOrClass(cause) or
      result = TIndefiniteObject(cause) or
      result = abstractValueOfType(any(PrimitiveType pt))
    )
  }
}
