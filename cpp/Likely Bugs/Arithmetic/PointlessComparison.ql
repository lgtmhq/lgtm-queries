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
 * @name Comparison result is always the same
 * @description When a comparison operation, such as x < y, always
 *              returns the same result, it means that the comparison
 *              is redundant and may mask a bug because a different
 *              check was intended.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/constant-comparison
 * @tags maintainability
 *       readability
 */
import cpp
private import semmle.code.cpp.rangeanalysis.PointlessComparison
import UnsignedGEZero

// Trivial comparisons of the form 1 > 0 are usually due to macro expansion.
// For example:
//
// #define PRINTMSG(val,msg) { if (val >= PRINTLEVEL) printf(msg); }
//
// So to reduce the number of false positives, we do not report a result if
// the comparison is in a macro expansion.
from
  ComparisonOperation cmp, SmallSide ss,
  float left, float right, boolean value,
  string reason
where
  not cmp.isInMacroExpansion() and
  reachablePointlessComparison(cmp, left, right, value, ss) and

  // Construct a reason for the message. Something like: x >= 5 and 3 >= y.
  exists (string cmpOp, string leftReason, string rightReason
  | ((ss = LeftIsSmaller()  and cmpOp = " <= ") or
     (ss = RightIsSmaller() and cmpOp = " >= ")) and
    leftReason = cmp.getLeftOperand().toString() + cmpOp + left.toString() and
    rightReason = right.toString() + cmpOp + cmp.getRightOperand().toString() and
    // If either of the operands is constant, then don't include it.
    (if cmp.getLeftOperand().isConstant()
       then if cmp.getRightOperand().isConstant()
              then none() // Both operands are constant so don't create a message.
              else reason = rightReason
       else if cmp.getRightOperand().isConstant()
              then reason = leftReason
              else reason = leftReason + " and " + rightReason)) and

  // Don't report results which have already been reported by UnsignedGEZero.
  not unsignedGEZero(cmp, _)
select
  cmp, "Comparison is always " + value.toString() + " because " + reason + "."
