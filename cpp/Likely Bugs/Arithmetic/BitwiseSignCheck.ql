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
 * @name Sign check of bitwise operation
 * @description Checking the sign of a bitwise operation often has surprising
 *              edge cases.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/bitwise-sign-check
 * @tags reliability
 *       correctness
 */
import default

from RelationalOperation e, BinaryBitwiseOperation lhs
where lhs = e.getLeftOperand() and
      lhs.getActualType().(IntegralType).isSigned() and
      forall(int op | op = lhs.(BitwiseAndExpr).getAnOperand().getValue().toInt() | op < 0) and
      e.getRightOperand().getValue() = "0" and
      not e.isAffectedByMacro()
select e, "Potential unsafe sign check of a bitwise operation."
