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
 * Provides the implementation of the PointlessSelfComparison query. The
 * query is implemented as a library, so that we can avoid producing
 * duplicate results in other similar queries.
 */

import cpp
import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis

/**
 * Holds if `cmp` is a comparison of the following form:
 *
 *     x == x
 *     (char)x != x
 *     x < (int)x
 *
 * Usually, the intention of the comparison is to detect whether the value
 * of `x` overflows when it is cast to a smaller type.  However, if
 * overflow is impossible then the comparison is either always true or
 * always false, depending on the type of comparison (`==`, `!=`, `<`, `>`,
 * `<=`, `>=`).
 */
predicate pointlessSelfComparison(ComparisonOperation cmp) {
  exists (Variable v, VariableAccess lhs, VariableAccess rhs
  | lhs = cmp.getLeftOperand() and
    rhs = cmp.getRightOperand() and
    lhs = v.getAnAccess() and
    rhs = v.getAnAccess() and
    not exists (lhs.getQualifier()) and // Avoid structure fields
    not exists (rhs.getQualifier()) and // Avoid structure fields
    not convertedExprMightOverflow(lhs) and
    not convertedExprMightOverflow(rhs))
}

/**
 * Holds if `cmp` is a floating point self comparison:
 *
 *     x == x
 *     x != x
 *
 * If the type of `x` is a floating point type, then such comparisons can
 * be used to detect if the value of `x` is NaN. Therefore, they should not
 * be reported as results of the PointlessSelfComparison query.
 */
predicate nanTest(EqualityOperation cmp) {
  pointlessSelfComparison(cmp) and
  exists (Type t
  | t = cmp.getLeftOperand().getType().getUnspecifiedType()
  | t instanceof FloatingPointType or
    t instanceof TemplateParameter)
}
