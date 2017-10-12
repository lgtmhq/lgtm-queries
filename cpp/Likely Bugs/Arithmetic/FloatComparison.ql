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
 * @name Equality test on floating-point values
 * @description Comparing results of floating-point computations with '==' or
 *              '!=' is likely to yield surprising results since floating-point
 *              computation does not follow the standard rules of algebra.
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/equality-on-floats
 * @tags reliability
 *       correctness
 */
import default

from EqualityOperation ro, Expr left, Expr right
where left = ro.getLeftOperand() and right = ro.getRightOperand() and
      ro.getAnOperand().getExplicitlyConverted().getType().getUnderlyingType() instanceof FloatingPointType and
      not ro.getAnOperand().isConstant() and // comparisons to constants generate too many false positives
      not left.(VariableAccess).getTarget() = right.(VariableAccess).getTarget() // skip self comparison
select ro, "Equality test on floating point values may not behave as expected."
