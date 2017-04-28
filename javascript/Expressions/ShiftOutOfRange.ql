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
 * @name Shift out of range
 * @description The shift operators '<<', '>>' and '>>>' only take the five least significant bits of their
 *              right operand into account. Thus, it is not possible to shift by more than 31 bits.
 * @kind problem
 * @problem.severity error
 * @tags reliability
 *       correctness
 *       external/cwe/cwe-197
 * @precision very-high
 */

import javascript

from ShiftExpr shift
where shift.getRightOperand().getIntValue() > 31
select shift, "Shift out of range."