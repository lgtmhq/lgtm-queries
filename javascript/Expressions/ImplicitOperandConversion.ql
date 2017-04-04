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
 * @name Implicit operand conversion
 * @description Relying on implicit conversion of operands is error-prone and makes code
 *              hard to read.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       readability
 * @precision high
 */

import javascript
import semmle.javascript.flow.Analysis
private import semmle.javascript.flow.InferredTypes

/** Holds if the `i`th operand of `parent` is interpreted as a number. */
predicate convertToNumber(Expr parent, int i) {
  (parent instanceof BitwiseExpr or
   parent instanceof ArithmeticExpr and not parent instanceof AddExpr) and
  i in [0..1]
}

/** Holds if the `i`th operand of `parent` is interpreted as an object. */
predicate convertToObject(Expr parent, int i) {
  parent instanceof InExpr and i = 1 or
  parent instanceof InstanceofExpr and i = 0
}

/**
 * Holds if `v` is an abstract value for `e` computed by the flow analysis,
 * and `e` occurs in a syntactic position where any concrete value represented
 * by `v` would be converted to type `convType` at runtime, but that conversion
 * is unlikely to be intentional.
 *
 * Typical examples of unlikely conversions include arithmetic comparisons involving
 * an object operand: the object will be converted to a number, which is very likely
 * to yield `NaN`.
 */
predicate unlikelyConversion(AnalyzedFlowNode e, AbstractValue v, string convType) {
  exists (Expr parent, int i | e = parent.getChildExpr(i) and v = e.getAValue() |
    // property names in `in` expressions should be strings or numbers
    parent instanceof InExpr and i = 0 and
    not (v.getType() = TTString() or v.getType() = TTNumber()) and
    convType = "string" or

    // property names in index expressions should be booleans, strings or numbers
    parent instanceof IndexExpr and i = 1 and
    not exists (InferredType t | t = v.getType() |
      t = TTBoolean() or t = TTString() or t = TTNumber()
    ) and
    convType = "string" or

    // operands of arithmetic operations should be booleans, numbers or Dates
    convertToNumber(parent, i) and
    not v.isCoercibleToNumber() and
    convType = "number" or

    // if an operand is converted to an object, it shouldn't be a primitive value
    convertToObject(parent, i) and
    not v.getType() instanceof NonPrimitiveType and
    convType = "object" or

    // the right hand operand of `instanceof` should be a function or class
    parent instanceof InstanceofExpr and i = 1 and
    not exists (InferredType t | t = v.getType() | t = TTFunction() or t = TTClass()) and
    convType = "function" or

    // the operands of `+` should not be null or undefined
    parent instanceof AddExpr and
    forall (InferredType tp | tp = v.getType() | tp = TTNull() or tp = TTUndefined()) and
    convType = "number or string" or

    // the operands of a relational comparison should be strings, numbers, or Dates
    exists (RelationalComparison rel | parent = rel |
      not exists (InferredType tp | tp = v.getType() |
        tp = TTString() or tp = TTNumber() or tp = TTDate()
      ) and
      convType = "number or string"
    )
  )
}

from AnalyzedFlowNode e, string convType
where unlikelyConversion(e, _, convType) and
      forall (AbstractValue v | v = e.getAValue() | unlikelyConversion(e, v, _))
select e, "This expression will be implicitly converted from " +
          e.ppTypes() + " to " + convType + "."