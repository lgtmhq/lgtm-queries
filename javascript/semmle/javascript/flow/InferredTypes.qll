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
 * Types inferred by the flow analysis, represented as type tags.
 *
 * These type tags are similar to the type tags returned by `typeof`,
 * except that
 *
 *   - `null` has type tag `null`, not `object`;
 *   - classes have type tag `class`, not `function`;
 *   - `Date` objects have type tag `date`, not `object`.
 *
 * We treat `Date` objects separately since they have some semantic
 * peculiarities; in particular, their primitive coercion yields
 * a number (not a string, as for most other objects).
 */

newtype TypeTag = TTNull() or TTUndefined() or TTBoolean() or TTNumber() or TTString()
               or TTFunction() or TTClass() or TTDate() or TTObject()

/**
 * A `typeof` tag, that is, a possible result of the `typeof` operator.
 */
class TypeofTag extends string {
  TypeofTag() {
    this = "undefined" or this = "boolean" or this = "number" or this = "string" or
    this = "function" or this = "object" or this = "symbol"
  }
}

/**
 * A type inferred by the flow analysis.
 */
class InferredType extends TypeTag {
  /** Gets a textual representation of this element. */
  abstract string toString();

  /** Gets the `typeof` tag corresponding to this type. */
  abstract string getTypeofTag();
}

/**
 * A primitive type (that is, one of `null`, `undefined`,
 * `boolean`, `number` or `string`) inferred by the
 * flow analysis.
 */
class PrimitiveType extends InferredType {
  PrimitiveType() {
    this = TTNull() or this = TTUndefined() or
    this = TTBoolean() or this = TTNumber() or this = TTString()
  }

  override string getTypeofTag() {
    this = TTNull() and result = "object" or
    this = TTUndefined() and result = "undefined" or
    this = TTBoolean() and result = "boolean" or
    this = TTNumber() and result = "number" or
    this = TTString() and result = "string"
  }

  override string toString() {
    this = TTNull() and result = "null" or
    this = TTUndefined() and result = "undefined" or
    this = TTBoolean() and result = "boolean" or
    this = TTNumber() and result = "number" or
    this = TTString() and result = "string"
  }
}

/**
 * A non-primitive type (that is, one of `function`, `class`,
 * `date` or `object`) inferred by the flow analysis.
 */
class NonPrimitiveType extends InferredType {
  NonPrimitiveType() {
    this = TTFunction() or this = TTClass() or
    this = TTDate() or this = TTObject()
  }

  override string getTypeofTag() {
    this = TTFunction() and result = "function" or
    this = TTClass() and result = "function" or
    this = TTDate() and result = "object" or
    this = TTObject() and result = "object"
  }

  override string toString() {
    this = TTFunction() and result = "function" or
    this = TTClass() and result = "class" or
    this = TTDate() and result = "date" or
    this = TTObject() and result = "object"
  }
}

/**
 * INTERNAL: Only to be used by the flow analysis library.
 *
 * Gets a pretty-printed list of all type tags in alphabetical order.
 */
string ppAllTypeTags() {
  result = "boolean, class, date, function, null, number, object, string or undefined"
}