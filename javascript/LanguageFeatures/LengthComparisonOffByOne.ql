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
 * @name Off-by-one comparison against length
 * @description An array index is compared to be less than or equal to the 'length' property,
 *              and then used in an indexing operation that could be out of bounds.
 * @kind problem
 * @problem.severity warning
 * @tags reliability
 *       correctness
 *       logic
  *      external/cwe/cwe-193
  * @precision medium
 */

import javascript

/**
 * Holds if `cond` ensures that `index` is less than or equal to `array.length`.
 */
predicate lengthGuard(ConditionGuardNode cond, Variable index, Variable array) {
  exists (RelationalComparison cmp, PropAccess len |
    cmp instanceof GEExpr or cmp instanceof LEExpr |
    cmp = cond.getTest() and cond.getOutcome() = true and
    cmp.getGreaterOperand() = len and cmp.getLesserOperand() = index.getAnAccess() and
    len.accesses(array.getAnAccess(), "length")
  )
}

/**
 * Holds if `ea` is a read from `array[index]`, and `indexAccess` is the index expression.
 */
predicate elementRead(IndexExpr ea, Variable array, Variable index, VarAccess indexAccess) {
  ea.getBase() = array.getAnAccess() and
  ea.getIndex() = indexAccess and
  ea instanceof RValue and
  indexAccess = index.getAnAccess()
}

from ConditionGuardNode cond, Variable array, Variable index, IndexExpr ea, VarAccess indexAccess
where // there is a comparison `index <= array.length`
      lengthGuard(cond, index, array) and
      // there is a read from `array[index]`
      elementRead(ea, array, index, indexAccess) and
      // and the read is guarded by the comparison
      cond.dominates(indexAccess.getBasicBlock())
select cond.getTest(), "Off-by-one index comparison against length may lead to out-of-bounds $@.", ea, "read"