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
 * Types inferred by the flow analysis, represented as type tags.
 *
 * These type tags are similar to the type tags returned by `typeof`,
 * except that
 *
 *   - `null` has type tag `null`, not `object`;
 *   - classes have type tag `class`, not `function`;
 *   - Date objects have type tag `date`, not `object`.
 *
 * We treat Date objects separately since they have some semantic
 * peculiarities; in particular, their primitive coercion yields
 * a number (not a string, as for most other objects).
 */

predicate isPrimitiveTypeTag(string tag) {
  tag = "null" or tag = "undefined" or
  tag = "boolean" or tag = "number" or tag = "string"
}

predicate isNonPrimitiveTypeTag(string tag) {
  tag = "function" or tag = "class" or
  tag = "date" or tag = "object"
}

predicate isTypeTag(string tag) {
  isPrimitiveTypeTag(tag) or isNonPrimitiveTypeTag(tag)
}

/**
 * Helper predicate that returns a pretty-printed list of all type tags.
 */
string ppAllTypeTags() {
  result = "boolean, class, date, function, null, number, object, string or undefined"
}

/**
 * A type inferred by the flow analysis.
 */
class InferredType extends string {
  InferredType() {
    isTypeTag(this)
  }
}

/**
 * A primitive type (that is, one of `null`, `undefined`,
 * `boolean`, `number` or `string`) inferred by the
 * flow analysis.
 */
class PrimitiveType extends InferredType {
  PrimitiveType() {
    isPrimitiveTypeTag(this)
  }
}

/**
 * A non-primitive type (that is, one of `function`, `class`,
 * `date` or `object`) inferred by the flow analysis.
 */
class NonPrimitiveType extends InferredType {
  NonPrimitiveType() {
    isNonPrimitiveTypeTag(this)
  }
}
