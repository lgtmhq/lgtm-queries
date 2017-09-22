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
 * @name Possibly wrong buffer size in string copy
 * @description Calling 'strncpy' with the size of the source buffer
 *              as the third argument may result in a buffer overflow.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-676
 *       external/cwe/cwe-119
 *       external/cwe/cwe-251
 */
import default
import Buffer

predicate isSizePlus(Expr e, BufferSizeExpr baseSize, int plus)
{
  (
    // baseSize
    e = baseSize and plus = 0
  ) or exists(AddExpr ae, Expr operand1, Expr operand2, int plusSub |
    // baseSize + n or n + baseSize
    ae = e and
    operand1 = ae.getAnOperand() and
    operand2 = ae.getAnOperand() and
    operand1 != operand2 and
    isSizePlus(operand1, baseSize, plusSub) and
    plus = plusSub + operand2.getValue().toInt()
  ) or exists(SubExpr se, int plusSub |
    // baseSize - n
    se = e and
    isSizePlus(se.getLeftOperand(), baseSize, plusSub) and
    plus = plusSub - se.getRightOperand().getValue().toInt()
  )
}

predicate strncpyFunction(Function f, int argDest, int argSrc, int argLimit)
{
  exists(string name | name = f.getName() |
    (
      (
        name = "strcpy_s" or    // strcpy_s(dst, max_amount, src)
        name = "wcscpy_s" or    // wcscpy_s(dst, max_amount, src)
        name = "_mbscpy_s"      // _mbscpy_s(dst, max_amount, src)
      ) and
      argDest = 0 and
      argSrc = 2 and
      argLimit = 1
    ) or (
      (
        name = "strncpy" or     // strncpy(dst, src, max_amount)
        name = "strncpy_l" or   // strncpy_l(dst, src, max_amount, locale)
        name = "wcsncpy" or     // wcsncpy(dst, src, max_amount)
        name = "_wcsncpy_l" or  // _wcsncpy_l(dst, src, max_amount, locale)
        name = "_mbsncpy" or    // _mbsncpy(dst, src, max_amount)
        name = "_mbsncpy_l"     // _mbsncpy_l(dst, src, max_amount, locale)
      ) and
      argDest = 0 and
      argSrc = 1 and
      argLimit = 2
    )
  )
}

/**
 * Holds if `a` and `b` access the same value. 
 */
predicate sameAccess(Access a, Access b) {
  // same target
  a.getTarget() = b.getTarget() and
  
  // same qualifier
  (
    (
      not exists(a.(VariableAccess).getQualifier()) and
      not exists(b.(VariableAccess).getQualifier())
    ) or (
      sameAccess(a.(VariableAccess).getQualifier(), b.(VariableAccess).getQualifier())
    )
  )
}

from FunctionCall fc, int argDest, int argSrc, int argLimit, Access copyDest, Access copySource, Access takenSizeOf, BufferSizeExpr sizeExpr, int plus
where
  strncpyFunction(fc.getTarget(), argDest, argSrc, argLimit) and
  copyDest = fc.getArgument(argDest) and
  copySource = fc.getArgument(argSrc) and
  sizeExpr = fc.getArgument(argLimit).getAChild*() and
  isSizePlus(fc.getArgument(argLimit), sizeExpr, plus) and
  plus >= 0 and
  takenSizeOf = sizeExpr.getArg() and
  sameAccess(copySource, takenSizeOf) and // e.g. strncpy(x, y, strlen(y))
  not sameAccess(copyDest, takenSizeOf) // e.g. strncpy(y, y, strlen(y))
select fc, "Potentially unsafe call to strncpy; third argument should be size of destination."
