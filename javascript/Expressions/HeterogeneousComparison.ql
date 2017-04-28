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
 * @name Comparison between inconvertible types
 * @description An equality comparison between two values that cannot be meaningfully converted to
 *              the same type will always yield 'false', and an inequality comparison will always
 *              yield 'true'.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-570
 *       external/cwe/cwe-571
 * @precision high
 */

import javascript
import semmle.javascript.flow.Analysis
private import semmle.javascript.flow.InferredTypes

/**
 * Holds if `left` and `right` are the left and right operands, respectively, of `nd`, which is
 * a comparison.
 *
 * Besides the usual comparison operators, `switch` statements are also considered to be comparisons,
 * with the switched-on expression being the right operand and all case labels the left operands.
 */
predicate comparisonOperands(ASTNode nd, Expr left, Expr right) {
  exists (Comparison cmp | cmp = nd | left = cmp.getLeftOperand() and right = cmp.getRightOperand()) or
  exists (SwitchStmt switch | switch = nd | right = switch.getExpr() and left = switch.getACase().getExpr())
}

/**
 * Gets a type that `operand`, which is an operand of comparison `parent`,
 * could be converted to at runtime.
 */
InferredType convertedOperandType(ASTNode parent, AnalyzedFlowNode operand) {
  // strict equality tests do no conversion at all
  operand = parent.(StrictEqualityTest).getAChildExpr() and result = operand.getAType() or

  // switch behaves like a strict equality test
  exists (SwitchStmt switch | switch = parent |
    (operand = switch.getExpr() or operand = switch.getACase().getExpr()) and
    result = operand.getAType()
  ) or

  // non-strict equality tests convert booleans and strings to numbers, and equate undefined and null
  operand = parent.(NonStrictEqualityTest).getAChildExpr() and
  exists (InferredType tp | tp = operand.getAValue().getType() |
    result = tp or
    (tp = TTBoolean() and result = TTNumber()) or
    (tp = TTString() and
     // exclude cases where the string is guaranteed to coerce to NaN
     not exists(StringLiteral l | l = operand | not exists(l.getValue().toFloat())) and
     result = TTNumber()) or
    (tp = TTUndefined() and result = TTNull())
  ) or

  // relational operators convert their operands to numbers or strings
  operand = parent.(RelationalComparison).getAChildExpr() and
  exists (AbstractValue v | v = operand.getAValue() |
    result = v.getType() or
    v.isCoercibleToNumber() and result = TTNumber()
  )
}

/**
 * Holds if `left` and `right` are operands of comparison `cmp` having types
 * `leftTypes` and `rightTypes`, respectively, but there is no
 * common type they coerce to.
 */
predicate isHeterogeneousComparison(ASTNode cmp, AnalyzedFlowNode left, AnalyzedFlowNode right,
                                    string leftTypes, string rightTypes) {
  comparisonOperands(cmp, left, right) and
  not convertedOperandType(cmp, left) = convertedOperandType(cmp, right) and
  leftTypes = left.ppTypes() and rightTypes = right.ppTypes()
}

from ASTNode cmp, AnalyzedFlowNode left, AnalyzedFlowNode right, string leftTypes, string rightTypes
where isHeterogeneousComparison(cmp, left, right, leftTypes, rightTypes) and
      // don't flag unreachable code
      exists (left.getAType()) and exists (right.getAType())
select left, "This expression is of type " + leftTypes + ", but it is compared to $@.",
       right, "an expression of type " + rightTypes
